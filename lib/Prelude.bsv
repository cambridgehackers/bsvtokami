typedef enum {
   VoidValue
   } Void;

typedef enum {
   False, True
   } Bool deriving (Bits,Eq);

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif
module mkReg#(a v)(Reg#(a));
    method Action _write(a v);
    endmethod
endmodule

typeclass Bits#(type a, numeric type asz);
   function Bit#(asz) pack(a v);
   function a unpack(Bit#(asz) bits);
endtypeclass

function Bit#(0) $methodready(Bit#(1) m);
   return 1;
endfunction
function Void $finish();
endfunction

endpackage
