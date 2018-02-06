

function ActionValue#(a) get();
   return 0;
endfunction

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

module mkReg#(a v)(Reg#(a));
    method Action _write(a v);
    endmethod
endmodule

module main(Empty);
  Bit#(8) b = 22;
  let a = b;
  function tvar foo(tvar in);
     return in;
   endfunction
   let c = foo(a);
   Reg#(Bit#(8)) r1 <- mkReg(22);
   Reg#(Bit#(24)) r2 <- mkReg(17);
   Bit#(24) z = 0;
   let r0 <- mkReg(0);
   rule rule1;
      r1 <= a;
      let v <- get();
      let d = foo(z);
      begin
         r2 <= d;
      end
      Bit#(24) r2_v = r2;
   endrule
   Reg#(Bit#(24)) r3 <- mkReg(42);
   rule rule2;
       r3._write(z);
   endrule
endmodule
