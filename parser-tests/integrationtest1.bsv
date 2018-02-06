import Vector::*;
import Ehr::*;

module mkTest1();
    Reg#(Bit#(32)) s <- mkReg(0);
    Vector#(32,Reg#(Bool)) s2 <- replicateM(mkReg(True));

    Reg#(Bit#(6)) i <- mkReg(12);

    rule nasty;
        let a <- $read(17);
        i <= i+1;
        $display("%d\n", i);
    endrule

    rule dangerous;
        s2[i]<=False;
        $display("Not locked");
    endrule

    rule dangerous2;
        s[i]<=1;
        $display("Not locked");
    endrule

      rule rl_rdata if (axiMaster.rready() == 1);
	 axiMaster.rlast(rdata.last?1:0); // added

      endrule

    rule another_rule;
      let memorySize = bramConfig.memorySize == 0 ? 2**valueOf(asz) : bramConfig.memorySize;
    endrule

    method apost = Bit#(17)'(22);
    method bar = 22;
    method foo(int x) = x * 17;
    method Action wid(Bit#(6) tag); /* no wid method */ endmethod //

endmodule

interface AxiStreamMaster#(numeric type dsz);
    method Bit#(dsz)              tdata();
    method Bit#(TDiv#(dsz,8))     tkeep();
    method Bit#(1)                tlast();
    (* prefix = "" *)method Action tready(    (* port="tready" *)  Bit#(1) v);
    method Bit#(1)                tvalid();
endinterface
  
import "BVI" OBUFDS =
module vMkOBUFDS#(Bit#(1) i)(DiffPair);
   default_clock clk();
   default_reset reset();

   port I = i;

   method O p;
   method OB n;

   path(I, O);
   path(I, OB);

   schedule (p, n) CF (p, n);

endmodule: vMkOBUFDS
