package GCD;

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

(* nogen *)
module mkReg#(a v)(Reg#(a));
    method Action _write(a v);
    endmethod
endmodule

interface ArithIO#(type a); 
    method Action start (a n, a m); 
    method a result; 
endinterface: ArithIO 

module mkGCD(ArithIO#(Bit#(32))); 
   Reg#(Bit#(32)) n <- mkReg(0); 
   Reg #(Bit#(32)) m <- mkReg(0); 

   rule swap (n > m && m != 0); 
      n <= m; 
      m <= n; 
   endrule 

   rule sub (n <= m && m != 0); 
      m <= m - n; 
   endrule 

   method Action start(Bit#(32) in_n, Bit#(32) in_m) if (m == 0); 
      action 
         n <= in_n; 
         m <= in_m; 
      endaction 
   endmethod: start 

   method Bit#(32) result() if (m == 0); 
      result = n; 
   endmethod: result 
endmodule: mkGCD 

// module main(Empty);
//       Reg#(Bit#(size_t)) n <- mkReg(60); 
//       Reg #(Bit#(size_t)) m <- mkReg(12); 
         
//       rule swap (n > m && m != 0); 
//                      n <= m; 
//                      m <= n; 
//                      $display("swap m=%d n=%d\n", m, n);
//       endrule 
         
//       rule sub (n <= m && m != 0); 
//                      m <= m - n; 
//                      $display("sub m=%d n=%d\n", m, n);
//       endrule 
// endmodule

// endpackage: GCD
