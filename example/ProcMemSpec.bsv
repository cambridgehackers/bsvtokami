import DefaultValue::*;
import RegFile::*;

typedef 32 DataSz;
typedef 32 AddrSz;
typedef 32 InstrSz;

typedef 32 NumRegs;
typedef TLog#(NumRegs) RegFileSz;
typedef 8 NumInstrs;
typedef TLog#(NumInstrs) PgmSz;

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
   method Bool isOp(Bit#(InstrSz) inst, OpK op);
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

interface Memory;
   method ActionValue#(Bit#(DataSz)) doMem(MemRq req);
endinterface

(* synthesize *)
module mkMemory(Memory);
   RegFile#(Bit#(AddrSz),Bit#(DataSz)) mem <- mkRegFileFull();
   method ActionValue#(Bit#(DataSz)) doMem(MemRq req);
      if (req.isLoad == 1'b1) begin
	 Bit#(AddrSz) addr = req.addr;
	 Bit#(DataSz) ldval = mem.sub(addr);
	 return ldval;
	 end
      else begin
	 Bit#(AddrSz) addr = req.addr;
	 Bit#(DataSz) newval = req.data;
	 mem.upd(addr, newval);
	 Bit#(DataSz) placeholder = mem.sub(addr);
	 return placeholder;
      end
   endmethod
endmodule

interface ToHost;
   method Action toHost(Bit#(DataSz) val);
endinterface

(* synthesize *)
module procSpec#(RegFile#(Bit#(PgmSz),Bit#(InstrSz)) pgm,
		 Decoder dec,
		 Executer exec,
		 ToHost tohost)(Empty);
   Reg#(Bit#(PgmSz)) pc <- mkRegU();
   RegFile#(Bit#(RegFileSz), Bit#(DataSz)) rf <- mkRegFileFull();
   Reg#(Bit#(2)) stage <- mkRegU();

   Reg#(OpK)      d2e_op <- mkRegU();
   Reg#(OpArithK) d2e_arithOp <- mkRegU();
   Reg#(Bit#(RegFileSz)) d2e_src1 <- mkRegU();
   Reg#(Bit#(RegFileSz)) d2e_src2 <- mkRegU();
   Reg#(Bit#(RegFileSz)) d2e_dst <- mkRegU();
   Reg#(Bit#(AddrSz)) d2e_addr <- mkRegU();

   Reg#(Bit#(RegFileSz)) e2w_dst <- mkRegU();
   Reg#(Bit#(DataSz))    e2w_val <- mkRegU();

   rule doDecode if (stage == 2'd0);
     Bit#(InstrSz) inst = pgm.sub(pc);
      d2e_op <= dec.getOp(inst);
      d2esrc1 <= dec.getSrc1(inst);
      d2e_src2 <= dec.getSrc2(inst);
      d2e_dst <= dec.getDst(inst);

      stage <= 2'd1;
   endrule

   rule doExec if (stage == 2'd1);

      Bit#(DataSz) val1 = rf.sub(d2e_src1);
      Bit#(DataSz) val2 = rf.sub(d2e_src2);
      Bit#(DataSz) dval = exec.execArith(d2e_op, val1, val2);

      e2w_dst <= d2e_dst;
      e2w_val <= dval;

      stage <= 2'd2;
   endrule

   rule doWriteBack if (stage == 2'd2);

      rf.upd(e2w_dst, e2w_val);

      pc <= pc + 1;

      stage <= 2'd0;
   endrule

//    rule doLoad if (dec.isOp(pgm.sub(pc),opLd));
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(AddrSz) addr = dec.getAddr(inst);
//       Bit#(RegFileSz) dst = dec.getDst(inst);
//       Bit#(DataSz) val <- mem.doMem(MemRq { isLoad: 1'b1, addr: addr, data: 32'd0 });
//       rf.upd(dst, val);
//       pc <= pc + 16'd1;
//    endrule

//    rule doStore if (dec.isOp(pgm.sub(pc),opSt));
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(AddrSz) addr = dec.getAddr(inst);
//       Bit#(RegFileSz) src = dec.getSrc1(inst);
//       Bit#(DataSz) val = rf.sub(src);
//       Bit#(DataSz) unused <- mem.doMem(MemRq { isLoad: 1'b0, addr: addr, data: val });
//       pc <= pc + 16'd1;
//    endrule

//    rule doHost if (dec.isOp(pgm.sub(pc),opTh));
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(RegFileSz) src1 = dec.getSrc1(inst);
//       Bit#(DataSz) val1 = rf.sub(src1);

//       tohost.toHost(val1);
//       pc <= pc + 16'd1;
//    endrule

endmodule
