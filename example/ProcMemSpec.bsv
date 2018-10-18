import DefaultValue::*;
import RegFile::*;
import Vector::*;


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

interface Decoder#(numeric type instsz, numeric type rfsz, numeric type addrsz);
   method OpK getOp(Bit#(instsz) inst);
   method OpArithK getArithOp(Bit#(instsz) inst);
   method Bit#(rfsz) getSrc1(Bit#(instsz) inst);
   method Bit#(rfsz) getSrc2(Bit#(instsz) inst);
   method Bit#(rfsz) getDst(Bit#(instsz) inst);
   method Bit#(addrsz) getAddr(Bit#(instsz) inst);
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif
module mkDecoder(Decoder#(instsz, rfsz, addrsz));
endmodule

interface Executer#(numeric type instsz, numeric type datasz);
   method Bit#(datasz) execArith(OpArithK op, Bit#(datasz) val1, Bit#(datasz) val2);
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif
module mkExecuter(Executer#(instsz, datasz));
endmodule

typedef struct {
   Bit#(1) isLoad;
   Bit#(addrsz) addr;
   Bit#(datasz) data;
   } MemRq#(numeric type addrsz, numeric type datasz) deriving (Bits);

interface Memory#(numeric type addrsz, numeric type datasz);
   method ActionValue#(Bit#(datasz)) doMem(MemRq#(addrsz, datasz) req);
endinterface

module mkMemory(Memory#(addrsz, datasz));
   RegFile#(Bit#(addrsz), Bit#(datasz)) mem <- mkRegFileFull();
   method ActionValue#(Bit#(datasz)) doMem(MemRq#(addrsz, datasz) req);
      if (req.isLoad == 1'b1) begin
	 Bit#(addrsz) addr = req.addr;
	 Bit#(datasz) ldval = mem.sub(addr);
	 return ldval;
	 end
      else begin
	 Bit#(addrsz) addr = req.addr;
	 Bit#(datasz) newval = req.data;
	 void unused <- mem.upd(addr, newval);
	 Bit#(datasz) placeholder = mem.sub(addr);
	 return placeholder;
      end
   endmethod
endmodule

interface ToHost#(numeric type datasz);
   method Action toHost(Bit#(datasz) val);
endinterface

typedef struct {
   Bit#(pgmsz) pcInit;
   Vector#(rfsz, Bit#(datasz)) rfInit;
   Vector#(pgmsz, Bit#(instsz)) pgmInit;
   } ProcInit#(numeric type addrsz, numeric type pgmsz, numeric type instsz, numeric type rfsz, numeric type datasz) deriving (Bits);

module procSpec#(ProcInit#(addrsz, pgmsz, instsz, rfsz, datasz) procInit,
		 Decoder#(instsz, rfsz, addrsz) dec,
		 Executer#(instsz, datasz) exec,
		 ToHost#(datasz) tohost)(Empty)
   provisos (Bits#(Bit#(instsz), instsz), Bits#(Bit#(datasz), datasz), DefaultValue#(Bit#(datasz)));
   Reg#(Bit#(pgmsz)) pc <- mkReg(procInit.pcInit);
   RegFile#(Bit#(rfsz), Bit#(datasz)) rf <- mkRegFileFull();
   Memory#(addrsz, datasz) mem <- mkMemory();
   RegFile#(Bit#(pgmsz), Bit#(instsz)) pgm <- mkRegFileFull(); //(procInit.pgmInit);

   Bit#(instsz) inst = pgm.sub(pc);

   OpK op = dec.getOp(inst);
   rule doArith if (op == opArith);
      Bit#(instsz) inst = pgm.sub(pc);
      OpK op = dec.getOp(inst);
      Bit#(rfsz) src1 = dec.getSrc1(inst);
      Bit#(rfsz) src2 = dec.getSrc2(inst);
      Bit#(rfsz) dst = dec.getDst(inst);
      Bit#(datasz) val1 = rf.sub(src1);
      Bit#(datasz) val2 = rf.sub(src2);
      Bit#(datasz) dval = exec.execArith(op, val1, val2);
      void unused <- rf.upd(dst, dval);
      pc <= pc + 1;
   endrule

   rule doLoad if (op == opLd);
      Bit#(instsz) inst = pgm.sub(pc);
      Bit#(addrsz) addr = dec.getAddr(inst);
      Bit#(rfsz) dst = dec.getDst(inst);
      Bit#(datasz) val <- mem.doMem(MemRq { isLoad: 1'b1, addr: addr, data: defaultValue });
      rf.upd(dst, val);
      pc <= pc + 1;
   endrule

   rule doStore if (op == opSt);
      Bit#(instsz) inst = pgm.sub(pc);
      Bit#(addrsz) addr = dec.getAddr(inst);
      Bit#(rfsz) src = dec.getSrc1(inst);
      Bit#(datasz) val = rf.sub(src);
      Bit#(datasz) unused <- mem.doMem(MemRq { isLoad: 1'b0, addr: addr, data: val });
      pc <= pc + 1;
   endrule

   rule doHost if (op == opTh);
      Bit#(instsz) inst = pgm.sub(pc);
      Bit#(rfsz) src1 = dec.getSrc1(inst);
      Bit#(datasz) val1 = rf.sub(src1);
      
      void unused <- tohost.toHost(val1);
      pc <= pc + 1;
   endrule

endmodule
