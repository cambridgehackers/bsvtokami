import DefaultValue::*;
import RegFile::*;
import Vector::*;

typedef 32 DataSz;
typedef 32 AddrSz;
typedef 32 InstrSz;
typedef 32 RegFileSz;
typedef 16 PgmSz;

Bit#(2) opArith = 2'b00;
Bit#(2) opLd = 2'b01;
Bit#(2) opSt = 2'b10;
Bit#(2) opTh = 2'b11;

typedef Bit#(2) OpK;

Bit#(2) opArithAdd = 2'b00;
Bit#(2) opArithSub = 2'b01;
Bit#(2) opArithMul = 2'b10;
Bit#(2) opArithDiv = 2'b11;

typedef Bit#(2) OpArithK;

interface Decoder;
   method OpK getOp(Bit#(InstrSz) inst);
   method OpArithK getArithOp(Bit#(InstrSz) inst);
   method Bit#(RegFileSz) getSrc1(Bit#(InstrSz) inst);
   method Bit#(RegFileSz) getSrc2(Bit#(InstrSz) inst);
   method Bit#(RegFileSz) getDst(Bit#(InstrSz) inst);
   method Bit#(AddrSz) getAddr(Bit#(InstrSz) inst);
endinterface

interface Executer;
   method Bit#(DataSz) execArith(OpArithK op, Bit#(DataSz) val1, Bit#(DataSz) val2);
endinterface

typedef struct {
   Bit#(1) isLoad;
   Bit#(AddrSz) addr;
   Bit#(DataSz) data;
   } MemRq deriving (Bits);

// work around bsvtokami type inference deficiencies
interface ProcRegFile;
   method Bit#(DataSz) sub(Bit#(AddrSz) idx);
   method Action upd(Bit#(AddrSz) idx, Bit#(DataSz) v);
endinterface

module mkProcRegFile(ProcRegFile);
   method Bit#(DataSz) sub(Bit#(AddrSz) idx);
      return 0;
   endmethod
   method Action upd(Bit#(AddrSz) idx, Bit#(DataSz) v);
   endmethod
endmodule

interface Memory;
   method ActionValue#(Bit#(DataSz)) doMem(MemRq req);
endinterface

module mkMemory(Memory);
   ProcRegFile mem <- mkProcRegFile();
   method ActionValue#(Bit#(DataSz)) doMem(MemRq req);
      if (req.isLoad == 1'b1) begin
	 Bit#(AddrSz) addr = req.addr;
	 Bit#(DataSz) ldval = mem.sub(addr);
	 return ldval;
	 end
      else begin
	 Bit#(AddrSz) addr = req.addr;
	 Bit#(DataSz) newval = req.data;
	 void unused <- mem.upd(addr, newval);
	 Bit#(DataSz) placeholder = mem.sub(addr);
	 return placeholder;
      end
   endmethod
endmodule

interface ToHost;
   method Action toHost(Bit#(DataSz) val);
endinterface

typedef struct {
   Bit#(PgmSz) pcInit;
   Vector#(RegFileSz, Bit#(DataSz)) rfInit;
   Vector#(PgmSz, Bit#(InstrSz)) pgmInit;
   } ProcInit deriving (Bits);

module procSpec#(ProcInit procInit,
		 Decoder dec,
		 Executer exec,
		 ToHost tohost)(Empty);
   Reg#(Bit#(PgmSz)) pc <- mkReg(procInit.pcInit);
   RegFile#(Bit#(RegFileSz), Bit#(DataSz)) rf <- mkRegFileFull();
   Memory mem <- mkMemory();
   RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm <- mkRegFileFull(); //(procInit.pgmInit);

   Bit#(InstrSz) inst = pgm.sub(pc);

   OpK op = dec.getOp(inst);
   rule doArith if (op == opArith);
      Bit#(InstrSz) inst = pgm.sub(pc);
      OpK op = dec.getOp(inst);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) src2 = dec.getSrc2(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      Bit#(DataSz) val1 = rf.sub(src1);
      Bit#(DataSz) val2 = rf.sub(src2);
      Bit#(DataSz) dval = exec.execArith(op, val1, val2);
      void unused <- rf.upd(dst, dval);
      pc <= pc + 1;
   endrule

   rule doLoad if (op == opLd);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(AddrSz) addr = dec.getAddr(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      Bit#(DataSz) val <- mem.doMem(MemRq { isLoad: 1'b1, addr: addr, data: defaultValue });
      rf.upd(dst, val);
      pc <= pc + 1;
   endrule

   rule doStore if (op == opSt);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(AddrSz) addr = dec.getAddr(inst);
      Bit#(RegFileSz) src = dec.getSrc1(inst);
      Bit#(DataSz) val = rf.sub(src);
      Bit#(DataSz) unused <- mem.doMem(MemRq { isLoad: 1'b0, addr: addr, data: val });
      pc <= pc + 1;
   endrule

   rule doHost if (op == opTh);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(DataSz) val1 = rf.sub(src1);

      void unused <- tohost.toHost(val1);
      pc <= pc + 1;
   endrule

endmodule
