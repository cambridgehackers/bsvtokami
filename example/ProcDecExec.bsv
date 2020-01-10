
import FIFOF::*;
import RegFile::*;
import ProcMemSpec::*;
import PipelinedProc::*;
import Vector::*;

interface NoMethods;
endinterface

module NoMethods mkDecExecSep(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		     Decoder dec,
		     Executer exec,
		     Memory mem,
                     Reg#(Vector#(NumRegs, Bit#(DataSz))) rf);
   FIFOF#(D2E) d2eFifo <- mkFIFOF();
   FIFOF#(E2W) e2wFifo <- mkFIFOF();

   Reg#(Bit#(PgmSz)) decoder_pc <- mkRegU;
   Reg#(Vector#(NumRegs, Bool)) sbFlags <- mkRegU();

   rule decode when (!d2eFifo.notFull());
      Bit#(InstrSz) inst = pgm.sub(decoder_pc);
      OpK op = dec.getOp(inst);
      OpArithK arithOp = dec.getArithOp(inst);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) src2 = dec.getSrc2(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      Bit#(AddrSz) addr = dec.getAddr(inst);

      D2E decoded = D2E {
         op: op, arithOp: arithOp, src1: src1, src2: src2, dst: dst, addr: addr, pc: decoder_pc
         };
      void enq <- d2eFifo.enq(decoded);
      decoder_pc <= decoder_pc + 3'd1;

   endrule

   D2E d2e = d2eFifo.first();
   rule executeArith when (d2eFifo.notEmpty()
                         && !sbFlags[d2e.src1]
                         && !sbFlags[d2e.src2]
                        );
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(RegFileSz) src2 = d2e.src2;
      Bit#(RegFileSz) dst = d2e.dst;
      OpArithK arithOp = d2e.arithOp;
      Bit#(DataSz) val1 = rf[src1];
      Bit#(DataSz) val2 = rf[src2];
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      Vector#(NumRegs, Bool) flags = sbFlags;
      //flags[dst] = True;
      sbFlags <= flags;
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
   endrule

   E2W e2w = e2wFifo.first();
      rule writeBack when (sbFlags[e2w.idx]);
         void e2wDeq <- e2wFifo.deq();
	 void d2eDeq <- d2eFifo.deq();

	 rf[e2w.idx] <= e2w.val;
	 Vector#(NumRegs, Bool) flags = sbFlags;
	 flags[e2w.idx] = False;
	 sbFlags <= flags;
      endrule

endmodule
