
import FIFO::*;
import FIFOF::*;
import RegFile::*;
import ProcMemSpec::*;
import PipelinedProc::*;

interface NoMethods;
endinterface

module mkDecExec#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		  Decoder dec,
                  Executer exec)(NoMethods);
   Reg#(Bit#(PgmSz)) pc <- mkRegU();
   FIFO#(E2W) e2wFifo <- mkFIFO(),
   Reg#(Vector#(NumRegs, Bit#(DataSz))) rf <- mkRegU();
   //RegFile#(Bit#(RegFileSz), Bool) sbFlags <- mkRegFileFull();

   rule decexecArith if (dec.isOp(pgm.sub(pc), opArith)
			//&& !sbFlags.sub(dec.getSrc1(pgm.sub(pc)))
			//&& !sbFlags.sub(dec.getSrc2(pgm.sub(pc)))
			);
      Bit#(InstrSz) inst = pgm.sub(pc);
      Bit#(RegFileSz) src1 = dec.getSrc1(inst);
      Bit#(RegFileSz) src2 = dec.getSrc2(inst);
      Bit#(RegFileSz) dst = dec.getDst(inst);
      OpArithK arithOp = dec.getArithOp(inst);
      Bit#(DataSz) val1 = rf[src1];
      Bit#(DataSz) val2 = rf[src2];
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      //void unused <- sbFlags.upd(dst, True);
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
      pc <= pc + 1;
   endrule

//    rule decexecLd if (dec.isOp(pgm.sub(pc), opLd)
// 			&& !sbFlags.sub(dec.getDst(pgm.sub(pc)))
// 			);
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(RegFileSz) src1 = dec.getSrc1(inst);
//       Bit#(RegFileSz) dst = dec.getDst(inst);
//       Bit#(AddrSz) addr = dec.getAddr(inst);
//       Bit#(DataSz) val1 = rf[src1];
//       MemRq memrq = MemRq { isLoad: 1'b1, addr: addr, data: val1 };
//       Bit#(DataSz) ldVal <- mem.doMem(memrq);
//       void unused <- sbFlags.upd(dst, True);
//       E2W e2w = E2W { idx: dst, val: ldVal };
//       void enq <- e2wFifo.enq(e2w);
//       pc <= pc + 1;
//    endrule

//    rule decexecSt if (dec.isOp(pgm.sub(pc), opSt));
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(RegFileSz) src1 = dec.getSrc1(inst);
//       Bit#(AddrSz) addr = dec.getAddr(inst);
//       Bit#(DataSz) val1 = rf[src1];
//       MemRq memrq = MemRq { isLoad: 1'b0, addr: addr, data: val1 };
//       Bit#(DataSz) unused <- mem.doMem(memrq);
//       pc <= pc + 1;
//    endrule

//    rule decexecToHost if (dec.isOp(pgm.sub(pc), opTh)
// 			&& !sbFlags.sub(dec.getSrc1(pgm.sub(pc)))
// 			);
//       Bit#(InstrSz) inst = pgm.sub(pc);
//       Bit#(RegFileSz) src1 = dec.getSrc1(inst);
//       Bit#(DataSz) val1 = rf[src1];
//       void unused <- toHost.toHost(val1);
//       pc <= pc + 1;
//    endrule

endmodule

module mkDecExecSep#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		     Decoder dec,
		     Executer exec,
		     Memory mem,
                     Reg#(Vector#(NumRegs, Bit#(DataSz))) rf,
		     ToHost toHost)(NoMethods);
   FIFOF#(D2E) d2eFifo <- mkFIFOF();
   FIFO#(E2W) e2wFifo <- mkFIFO();

   Reg#(Bit#(PgmSz)) decoder_pc <- mkReg(16'h0);
   RegFile#(Bit#(RegFileSz), Bool) sbFlags <- mkRegFileFull();

   rule decode if (d2eFifo.notFull());
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
      decoder_pc <= decoder_pc + 16'd1;

   endrule

   D2E d2e = d2eFifo.first();
   rule executeArith if (d2eFifo.notEmpty()
                         && d2e.op == opArith
                         && !sbFlags.sub(d2e.src1)
                         && !sbFlags.sub(d2e.src2)
                        );
      D2E d2e = d2eFifo.first();
      void deq <- d2eFifo.deq();
      Bit#(RegFileSz) src1 = d2e.src1;
      Bit#(RegFileSz) src2 = d2e.src2;
      Bit#(RegFileSz) dst = d2e.dst;
      OpArithK arithOp = d2e.arithOp;
      Bit#(DataSz) val1 = rf[src1];
      Bit#(DataSz) val2 = rf[src2];
      Bit#(DataSz) execVal = exec.execArith(arithOp, val1, val2);
      void unused <- sbFlags.upd(dst, True);
      E2W e2w = E2W { idx: dst, val: execVal };
      void enq <- e2wFifo.enq(e2w);
   endrule

//    rule executeLoad if (d2e.op == opLd
//                          && !sbFlags.sub(d2e.src1)
//                          && !sbFlags.sub(d2e.dst)
//                         );
//       D2E d2e = d2eFifo.first();
//       void deq <- d2eFifo.deq();
//       Bit#(RegFileSz) src1 = d2e.src1;
//       Bit#(RegFileSz) dst = d2e.dst;
//       Bit#(AddrSz) addr = d2e.addr;
//       Bit#(DataSz) val1 = rf[src1];
//       MemRq memrq = MemRq { isLoad: 1'b1, addr: addr, data: 32'b0 };
//       Bit#(DataSz) ldVal <- mem.doMem(memrq);
//       void unused <- sbFlags.upd(dst, True);
//       E2W e2w = E2W { idx: dst, val: ldVal };
//       void enq <- e2wFifo.enq(e2w);
//    endrule

//    rule executeStore if (d2e.op == opSt
//                          && !sbFlags.sub(d2e.src1)
//                         );
//       D2E d2e = d2eFifo.first();
//       void deq <- d2eFifo.deq();
//       Bit#(RegFileSz) src1 = d2e.src1;
//       Bit#(AddrSz) addr = d2e.addr;
//       Bit#(DataSz) val1 = rf[src1];
//       MemRq memrq = MemRq { isLoad: 1'b0, addr: addr, data: val1 };
//       Bit#(DataSz) unused <- mem.doMem(memrq);
//    endrule

//    rule executeToHost if (d2e.op == opTh
//                          && !sbFlags.sub(d2e.src1)
//                         );
//       D2E d2e = d2eFifo.first();
//       void deq <- d2eFifo.deq();
//       Bit#(RegFileSz) src1 = d2e.src1;
//       Bit#(AddrSz) addr = d2e.addr;
//       Bit#(DataSz) val1 = rf[src1];
//       void unused <- toHost.toHost(val1);
//    endrule

endmodule
