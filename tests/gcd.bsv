package GCD;

typedef enum {
   False, True
   } Bool deriving (Bits,Eq);

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

(* nogen *)
module mkReg#(a v)(Reg#(a));
    method Action _write(a v);
    endmethod
endmodule

interface GCD#(type a);
    method Action set_n (a n);
    method Action set_m (a m);
    method a result;
endinterface: GCD

module mkGCD(GCD#(Bit#(32)));
   Reg#(Bit#(32)) n <- mkReg(0);
   Reg #(Bit#(32)) m <- mkReg(0);

   rule swap (n > m && m != 0);
      n <= m;
      m <= n;
   endrule

   rule sub (n <= m && m != 0);
      m <= m - n;
   endrule

   method Action set_n(Bit#(32) in_n) if (m == 0);
      action
         n <= in_n;
      endaction
   endmethod:
   method Action set_m(Bit#(32) in_m) if (m == 0);
      action
         m <= in_m;
      endaction
   endmethod:

   method Bit#(32) result() if (m == 0);
      return n;
   endmethod: result
endmodule: mkGCD

module mkMain(Empty);
   GCD#(Bit#(32)) gcd <- mkGCD();
   Reg#(Bit#(1)) started <- mkReg(0);
   rule rl_init;
   endrule
   rule rl_start if (started == 0);
      gcd.set_n(100);
      gcd.set_m(20);
      started <= 1;
   endrule
   rule rl_display;
      Bit#(32) v <- gcd.result();
   endrule
endmodule

// endpackage: GCD
