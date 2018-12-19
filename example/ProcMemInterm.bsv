
import FIFO::*;
import RegFile::*;

import ProcMemSpec::*;
import PipelinedProc::*;
import ProcDecExec::*;

module mkProcInterm#(RegFile#(Bit#(PgmSz), Bit#(InstrSz)) pgm,
		     Decoder dec,
		     Executer exec,
		     Memory mem,
		     ToHost toHost)(Empty);
   Reg#(Bit#(PgmSz)) pc <- mkReg(0);
   ProcRegs rf <- mkProcRegs();
   Scoreboard sb <- mkScoreboard();
   FIFO#(E2W) e2wFifo <- mkFIFO();
   Empty decexec <- mkDecExec(pgm, dec, exec, // sb,
      e2wFifo, rf, mem, toHost);
   Empty writeback <- mkPipelinedWriteback(e2wFifo, sb, rf);
endmodule
