package Prelude;

typedef enum {
   VoidValue
   } Void;

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

//`ifdef BSVTOKAMI
(* nogen *)
//`endif
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


function String integerToString(Integer m);
   return (String)'m;
endfunction

typeclass Literal #(type data_t);
   function data_t fromInteger(Integer x);
   function Bool   inLiteralRange(data_t target, Integer x);
endtypeclass

instance Literal#(Bit#(bsz));
   function Bit#(bsz) fromInteger(Integer x); return (Bit#(bsz))'x; endfunction
endinstance
instance Literal#(Int#(bsz));
   function Int#(bsz) fromInteger(Integer x); return (Int#(bsz))'x; endfunction
endinstance
instance Literal#(UInt#(bsz));
   function UInt#(bsz) fromInteger(Integer x); return (UInt#(bsz))'x; endfunction
endinstance

typeclass RealLiteral #(type data_t);
   function data_t fromReal(Real x);
endtypeclass

typeclass SizedLiteral #(type data_t, type size_t)
   dependencies (data_t determines size_t);
   function data_t fromSizedInteger(Bit#(size_t) x);
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
   function data_t \<< (data_t x1, data_t x2);
   function data_t \>> (data_t x1, data_t x2);
   function Bit#(1) msb (data_t x);
   function Bit#(1) lsb (data_t x);
endtypeclass

typeclass BitReduction #(type x, numeric type n);
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

typedef enum {
   False, True
   } Bool deriving (Bits,Eq);

typedef union tagged {
   a Valid;
   Void Invalid;
   } Maybe#(type a) deriving (Bits,Eq);

function Bool isValid(Maybe#(data_t) m);
   return (case (m) matches tagged Valid: return True; default: return False; endcase); 
endfunction

function data_t fromMaybe( data_t defaultval,
                           Maybe#(data_t) val ) ;
   return (case (m) matches tagged Valid .val: return val; default: return defaultval; endcase); 
endfunction

function Bit#(0) \$methodready (Bit#(1) m);
   return 1;
endfunction

function Void \$finish ();
endfunction

typedef struct {
		t1 tpl_1;
		t2 tpl_2;
   } Tuple2#(type t1, type t2) deriving (Bits);

function Tuple2#(t1, t2) tuple2(t1 x1, t2 x2);
   return Tuple2 { tpl_1: x1, tpl_2: x2 };
endfunction

typedef struct {
		t1 tpl_1;
		t2 tpl_2;
		t3 tpl_3;
   } Tuple3#(type t1, type t2, type t3) deriving (Bits);

function Tuple3#(t1, t2, t3) tuple3(t1 x1, t2 x2, t3 x3);
   return Tuple3 { tpl_1: x1, tpl_2: x2, tpl_3: x3 };
endfunction

typedef struct {
		t1 tpl_1;
		t2 tpl_2;
		t3 tpl_3;
		t4 tpl_4;
   } Tuple4#(type t1, type t2, type t3, type t4) deriving (Bits);

function Tuple4#(t1, t2, t3, t4) tuple4(t1 x1, t2 x2, t3 x3, t4 x4);
   return Tuple4 { tpl_1: x1, tpl_2: x2, tpl_3: x3, tpl_4: x4 };
endfunction

typeclass TupleSelector#(type t, type t1, type t2, type t3, type t4);
   function t1 tpl_1(t tpl);
   function t2 tpl_2(t tpl);
   function t3 tpl_3(t tpl);
   function t4 tpl_4(t tpl);
endtypeclass

instance TupleSelector#(Tuple2#(t1,t2), t1, t2, t3, t4);
   function t1 tpl_1(Tuple2#(t1,t2) tpl);
      return tpl.tpl_1;
   endfunction
   function t2 tpl_2(Tuple2#(t1,t2) tpl);
      return tpl.tpl_2;
   endfunction
endinstance
instance TupleSelector#(Tuple3#(t1,t2,t3), t1, t2, t3, t4);
   function t1 tpl_1(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_1;
   endfunction
   function t2 tpl_2(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_2;
   endfunction
   function t3 tpl_3(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_3;
   endfunction
endinstance
instance TupleSelector#(Tuple4#(t1,t2,t3,t4), t1, t2, t3, t4);
   function t1 tpl_1(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_1;
   endfunction
   function t2 tpl_2(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_2;
   endfunction
   function t3 tpl_3(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_3;
   endfunction
   function t4 tpl_3(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_4;
   endfunction
endinstance

interface Empty;
endinterface

module errorM#(String s)(Empty);
endmodule

function Action noAction(); endfunction

endpackage
