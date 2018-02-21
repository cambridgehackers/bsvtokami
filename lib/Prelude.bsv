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

typeclass Bits #(type a, numeric type n);
   function Bit#(n) pack(a x);
   function a unpack(Bit#(n) x);
endtypeclass

typeclass Eq #(type data_t);
   function Bool \== (data_t x, data_t y);
   function Bool \/= (data_t x, data_t y);
endtypeclass


typeclass Literal #(type data_t);
   function data_t fromInteger(Integer x);
   function Bool   inLiteralRange(data_t target, Integer x);
endtypeclass

typeclass RealLiteral #(type data_t);
   function data_t fromReal(Real x);
endtypeclass

typeclass SizedLiteral #(type data_t, type size_t)
   dependencies (data_t determines size_t);
   function data_t fromSizedInteger(Bit#(size_t);
endtypeclass

typeclass Arith#(type data_t)
   provisos (Literal#(data_t));
   function data_t \+ (data_t x, data_t y);
   function data_t \- (data_t x, data_t y);
   function data_t negate (data_t x);
   function data_t \* (data_t x, data_t y);
   function data_t \/ (data_t x, data_t y);
   function data_t \% (data_t x, data_t y);
   function data_t abs (data_t x);
   function data_t signum (data_t x);
   function data_t \** (data_t x, data_t y);
   function data_t exp_e (data_t x);
   function data_t log (data_t x);
   function data_t logb (data_t b, data_t x);
   function data_t log2 (data_t x);
   function data_t log10 (data_t x);
endtypeclass

typeclass Ord #(type data_t);
   function Bool \<  (data_t x, data_t y);
   function Bool \<= (data_t x, data_t y);
   function Bool \>  (data_t x, data_t y);
   function Bool \>= (data_t x, data_t y);
   function Ordering compare(data_t x, data_t y);
   function data_t min(data_t x, data_t y);
   function data_t max(data_t x, data_t y);
endtypeclass

typeclass Bounded #(type data_t);
   data_t minBound;
   data_t maxBound;
endtypeclass

typeclass Bitwise #(type data_t);
   function data_t \& (data_t x1, data_t x2);
   function data_t \| (data_t x1, data_t x2);
   function data_t \^ (data_t x1, data_t x2);
   function data_t \~^ (data_t x1, data_t x2);
   function data_t \^~ (data_t x1, data_t x2);
   function data_t invert (data_t x1);
   function data_t \<< (data_t x1, x2);
   function data_t \>> (data_t x1, x2);
   function Bit#(1) msb (data_t x);
   function Bit#(1) lsb (data_t x);
endtypeclass

typeclass BitReduction #(type x, numeric type n)
   function x#(1) reduceAnd (x#(n) d);
   function x#(1) reduceOr (x#(n) d);
   function x#(1) reduceXor (x#(n) d);
   function x#(1) reduceNand (x#(n) d);
   function x#(1) reduceNor (x#(n) d);
   function x#(1) reduceXnor (x#(n) d);
endtypeclass

typeclass BitExtend #(numeric type m, numeric type n, type x);  // n > m
   function x#(n) extend (x#(m) d);
   function x#(n) zeroExtend (x#(m) d);
   function x#(n) signExtend (x#(m) d);
   function x#(m) truncate (x#(n) d);
endtypeclass

// typedef enum { Sat_Wrap
// 	      ,Sat_Bound
// 	      ,Sat_Zero
// 	      ,Sat_Symmetric
// 	      } SaturationMode deriving (Bits, Eq);

// typeclass SaturatingArith#( type t);
//    function t satPlus (SaturationMode mode, t x, t y);
//    function t satMinus (SaturationMode mode, t x, t y);
//    function t boundedPlus  (t x, t y) = satPlus (Sat_Bound, x, y);
//    function t boundedMinus (t x, t y) = satMinus(Sat_Bound, x, y);
// endtypeclass

typeclass Alias#(type a, type b)
   dependencies (a determines b,
                 b determines a);
endtypeclass
      
typeclass FShow#(type t);
   function Fmt fshow(t value);
endtypeclass

function Bit#(0) $methodready(Bit#(1) m);
   return 1;
endfunction

function Void $finish();
endfunction

endpackage
