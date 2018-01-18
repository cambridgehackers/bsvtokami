

module mkTest(Empty);
  Bit#(8) b = 22;
  let a = b;
  function tvar foo(tvar in);
     return in;
   endfunction
   let c = foo(a);
   Reg#(Bit#(8)) r1;
   Reg#(Bit#(24)) r2;
   Bit#(24) z;
   rule r1;
      r1 <= a;
      let d = foo(z);
      begin
         r2 <= d;
      end
      Bit#(24) r2_v = r2;
   endrule
endmodule
