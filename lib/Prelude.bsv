package Prelude;

typedef enum {
   VoidValue
   } Void;

// B.2.20

interface Bit#(numeric type sz);
endinterface

interface Empty;
endinterface

interface Rule;
endinterface

interface Rules;
endinterface

(* nogen *)
function Rules emptyRules;
endfunction

module addRules#(Rules r) (Empty);
endmodule

(* nogen *)
function Rules rJoin(Rules x, Rules y);
endfunction

(* nogen *)
function Rules rJoinDescendingUrgency(Rules x, Rules y);
endfunction

(* nogen *)
function Rules rJoinMutuallyExclusive(Rules x, Rules y);
endfunction

(* nogen *)
function Rules rJoinExecutionOrder(Rules x, Rules y);
endfunction

(* nogen *)
function Rules rJoinConflictFree(Rules x, Rules y);
endfunction

// B.something

interface ReadOnly#(type a);
  method a _read();
endinterface

interface Reg#(type a);
  method a _read();
  method Action _write(a v);
endinterface

interface Wire#(type a);
  method a _read();
  method Action _write(a v);
endinterface

(* nogen *)
function Reg#(a_type) asReg(Reg#(a_type) regIfc);
   return regIfc;
endfunction

(* nogen *)
function a_type readReg(Reg#(a_type) regIfc);
   return regIfc._read();
endfunction

(* nogen *)
function Action writeReg(Reg#(a_atype) regIfc, a_type din);
   regIfc._write(din);
endfunction

//`ifdef BSVTOKAMI
(* nogen *)
//`endif
module mkReg#(data_t v)(Reg#(data_t));
    method Action _write(data_t v);
    endmethod
endmodule
module mkRegA#(data_t v)(Reg#(data_t));
    method Action _write(data_t v);
    endmethod
endmodule
module mkRegU(Reg#(data_t)) provisos (Bits#(data_t,datasz));
    method Action _write(data_t v);
    endmethod
endmodule

//FIXME
module mkCReg#(Integer depth, data_t v)(Reg#(data_t));
endmodule

(* nogen *)
module mkWire(Wire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule
(* nogen *)
module mkBypassWire(Wire#(element_type))
   provisos (Bits#(element_type, element_width));
endmodule

// D.4.6

module mkDWire#(a_type defaultval)(Wire#(element_type))
   provisos (Bits#(element_type, element_width));
endmodule

module mkUnsafeDWire#(a_type defaultval)(Wire#(element_type))
   provisos (Bits#(element_type, element_width));
endmodule

interface PulseWire;
     method Action send();
     method Bool _read();
endinterface

module mkPulseWire(PulseWire);
endmodule

(* nogen *)
function a id(a x);
   return x;
endfunction

(* nogen *)
function Bool \$guard(Bool cond);
   return False;
endfunction

(* nogen *)
function a when(Bool cond, a expr);
   $guard(cond);
   return expr;
endfunction

typeclass Bits #(type a, numeric type nsz);
(* nogen *)
   function Bit#(nsz) pack(a x);
(* nogen *)
   function a unpack(Bit#(nsz) x);
endtypeclass

typeclass Eq #(type data_t);
(* nogen *)
   function Bool \== (data_t x, data_t y);
(* nogen *)
   function Bool \/= (data_t x, data_t y);
endtypeclass


(* nogen *)
function String integerToString(Integer m);
   return (String)'m;
endfunction

typeclass Literal #(type data_t);
(* nogen *)
   function data_t fromInteger(Integer x);
(* nogen *)
   function Bool   inLiteralRange(data_t target, Integer x);
endtypeclass

instance Literal#(Bit#(bsz));
(* nogen *)
   function Bit#(bsz) fromInteger(Integer x); return (Bit#(bsz))'x; endfunction
endinstance
instance Literal#(Int#(bsz));
(* nogen *)
   function Int#(bsz) fromInteger(Integer x); return (Int#(bsz))'x; endfunction
endinstance
instance Literal#(UInt#(bsz));
(* nogen *)
   function UInt#(bsz) fromInteger(Integer x); return (UInt#(bsz))'x; endfunction
endinstance

typeclass RealLiteral #(type data_t);
(* nogen *)
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

typeclass BitReduction #(type x, numeric type nsz);
   function x#(1) reduceAnd (x#(nsz) d);
   function x#(1) reduceOr (x#(nsz) d);
   function x#(1) reduceXor (x#(nsz) d);
   function x#(1) reduceNand (x#(nsz) d);
   function x#(1) reduceNor (x#(nsz) d);
   function x#(1) reduceXnor (x#(nsz) d);
endtypeclass

typeclass BitExtend #(numeric type msz, numeric type nsz, type x);  // n > m
   function x#(nsz) extend (x#(msz) d);
   function x#(nsz) zeroExtend (x#(msz) d);
   function x#(nsz) signExtend (x#(msz) d);
   function x#(msz) truncate (x#(nsz) d);
endtypeclass

(* nogen *)
function Bool signedLT(a x, a y);
   return x < y;
endfunction
(* nogen *)
function Bool signedGE(a x, a y);
   return x >= y;
endfunction
(* nogen *)
function Bit#(asz) signedShiftRight(Bit#(asz) x, Bit#(bsz) shift);
   return x >> shift;
endfunction

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
   Bit#(1) Invalid;
   } Maybe#(type a) deriving (Bits,Eq);

function Bool isValid(Maybe#(data_t) val);
   case (val) matches tagged Valid: return True; default: return False; endcase
endfunction

function data_t fromMaybe( data_t defaultval,
                           Maybe#(data_t) val ) ;
   return (case (val) matches
	   tagged Valid .validval: validval;
	   tagged Invalid: defaultval;
      endcase);
endfunction

(* nogen *)
function data_t validValue(Maybe#(data_t) val ) ;
   return (case (val) matches
	   tagged Valid .validval: validval;
	   tagged Invalid: ?;
      endcase);
endfunction

(* nogen *)
function Bit#(0) \$methodready (Bit#(1) m);
   return 1;
endfunction

(* nogen *)
function Void \$display ( a x);
endfunction

(* nogen *)
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

(* nogen *)
function Tuple3#(t1, t2, t3) tuple3(t1 x1, t2 x2, t3 x3);
   return Tuple3 { tpl_1: x1, tpl_2: x2, tpl_3: x3 };
endfunction

typedef struct {
		t1 tpl_1;
		t2 tpl_2;
		t3 tpl_3;
		t4 tpl_4;
   } Tuple4#(type t1, type t2, type t3, type t4) deriving (Bits);

(* nogen *)
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
(* nogen *)
   function t1 tpl_1(Tuple2#(t1,t2) tpl);
      return tpl.tpl_1;
   endfunction
(* nogen *)
   function t2 tpl_2(Tuple2#(t1,t2) tpl);
      return tpl.tpl_2;
   endfunction
endinstance
instance TupleSelector#(Tuple3#(t1,t2,t3), t1, t2, t3, t4);
(* nogen *)
   function t1 tpl_1(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_1;
   endfunction
(* nogen *)
   function t2 tpl_2(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_2;
   endfunction
(* nogen *)
   function t3 tpl_3(Tuple3#(t1,t2,t3) tpl);
      return tpl.tpl_3;
   endfunction
endinstance
instance TupleSelector#(Tuple4#(t1,t2,t3,t4), t1, t2, t3, t4);
(* nogen *)
   function t1 tpl_1(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_1;
   endfunction
(* nogen *)
   function t2 tpl_2(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_2;
   endfunction
(* nogen *)
   function t3 tpl_3(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_3;
   endfunction
(* nogen *)
   function t4 tpl_4(Tuple4#(t1,t2,t3,t4) tpl);
      return tpl.tpl_4;
   endfunction
endinstance

interface Empty;
endinterface

function Action error(String msg);
endfunction

module errorM#(String s)(Empty);
endmodule

function Action noAction(); endfunction

// B.4.3

interface RWire#(type element_type) ;
   method Action wset(element_type datain) ;
   method Maybe#(element_type) wget() ;
endinterface: RWire

module mkRWireSBR(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

module mkUnsafeRWire(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

module mkRWire(RWire#(element_type))
   provisos (Bits#(element_type, element_width)) ;
endmodule

// B.5.4

(* nogen *)
function Bit#(1) parity(Bit#(nsz) v);
endfunction

(* nogen *)
function Bit#(nsz) reverseBits(Bit#(nsz) x);
endfunction

(* nogen *)
function Bit#(nsz) truncateLSB(Bit#(msz) x)
   provisos(Add#(nsz,ksz,msz));
   return Bit#(nsz)'(x >> valueOf(k));
endfunction

// 12.8.3

typedef union tagged {
        void     InvalidFile ;
        Bit#(31) MCD;
        Bit#(31) FD;
} File;

File stdin = tagged MCD 0;
File stdout = tagged MCD 1;
File stderr = tagged MCD 2;

endpackage
