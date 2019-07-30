package GCD;

interface GCD#(type a);
    method Action set_n (a n);
    method Action set_m (a m);
    method a result;
endinterface: GCD

module GCD#(Bit#(32)) mkGCD();
   Reg#(Bit#(32)) n <- mkRegU();
   Reg #(Bit#(32)) m <- mkRegU();

   rule swap when (n > m && m != 0);
      n <= m;
      m <= n;
   endrule

   rule sub when (n <= m && m != 0);
      m <= m - n;
   endrule

   method Action set_n(Bit#(32) in_n) when (m == 0);
       n <= in_n;
   endmethod
   method Action set_m(Bit#(32) in_m) when (m == 0);
       m <= in_m;
   endmethod

   method Bit#(32) result() when (m == 0);
      return n;
   endmethod: result
endmodule: mkGCD

module Empty mkMain();
   GCD#(Bit#(32)) gcd <- mkGCD();
   Reg#(Bit#(1)) started <- mkRegU();
   Reg#(Bit#(32)) dv <- mkRegU();
   rule rl_start when (started == 0);
      gcd.set_n(32'd100);
      gcd.set_m(32'd20);
      started <= 1;
   endrule
   rule rl_display;
      let v = gcd.result();
      dv <= v;
      finish();
   endrule
endmodule

endpackage: GCD
