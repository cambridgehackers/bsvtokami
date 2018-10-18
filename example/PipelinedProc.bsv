
import DefaultValue::*;
import FIFO::*;
import ProcMemSpec::*;
import Vector::*;

interface ProcRegFile#(numeric type rfsz, numeric type datasz);
   method Bit#(datasz) read1(Bit#(rfsz) r1);
   method Bit#(datasz) read2(Bit#(rfsz) r2);
   method Action write(Bit#(rfsz) r, Bit#(datasz) val);
endinterface

typedef struct {
   OpK op;
   OpArithK arithOp;
   Bit#(rfsz) src1;
   Bit#(rfsz) src2;
   Bit#(rfsz) dst;
   Bit#(addrsz) addr;
   Bit#(pgmsz) pc;
   } D2E#(numeric type addrsz, numeric type pgmsz, numeric type rfsz) deriving (Bits);

module mkPipelinedDecoder#(Bit#(pgmsz) pcInit,
			   Vector#(TExp#(pgmsz), Bit#(instsz)) pgmInit,
			   Decoder#(instsz, rfsz, addrsz) dec,
			   FIFO#(D2E#(addrsz, pgmsz, rfsz)) d2e)(Empty);
   Reg#(Bit#(pgmsz)) pc <- mkReg(pcInit);
   
   rule decode;
      Bit#(instsz) inst = pgmInit[pc];
      OpK op = dec.getOp(inst);
      OpArithK arithOp = dec.getArithOp(inst);
      Bit#(rfsz) src1 = dec.getSrc1(inst);
      Bit#(rfsz) src2 = dec.getSrc2(inst);
      Bit#(rfsz) dst = dec.getDst(inst);
      Bit#(addrsz) addr = dec.getAddr(inst);

      D2E#(addrsz, pgmsz, rfsz) decoded = D2E {
	 op: op, arithOp: arithOp, src1: src1, src2: src2, dst: dst, addr: addr, pc: pc
	 };
      d2e.enq(decoded);
      pc <= pc + 1;
   endrule
endmodule

interface Scoreboard#(numeric type rfsz);
   method Bool search1(Bit#(rfsz) sidx);
   method Bool search2(Bit#(rfsz) sidx);
   method Action insert(Bit#(rfsz) sidx);
   method Action remove(Bit#(rfsz) sidx);
endinterface

module mkScoreboard(Scoreboard#(rfsz));
   Reg#(Vector#(TExp#(rfsz), Bool)) sbFlags <- mkReg(defaultValue);
   
   method Bool search1(Bit#(rfsz) sidx);
      Bool flag = sbFlags[sidx];
      return flag;
   endmethod

   method Bool search2(Bit#(rfsz) sidx);
      Bool flag = sbFlags[sidx];
      return flag;
   endmethod

   method Action insert(Bit#(rfsz) nidx);
      Vector#(TExp#(rfsz), Bool) flags = sbFlags;
      flags[nidx] = True;
      sbFlags <= flags;
   endmethod

   method Action remove(Bit#(rfsz) nidx);
      Vector#(TExp#(rfsz), Bool) flags = sbFlags;
      flags[nidx] = False;
      sbFlags <= flags;
   endmethod
endmodule

