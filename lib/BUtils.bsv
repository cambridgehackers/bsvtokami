// Copyright (c) 2007--2009 Bluespec, Inc.  All rights reserved.
// $Revision: 34721 $
// $Date: 2015-11-01 03:26:17 +0000 (Sun, 01 Nov 2015) $

package BUtils;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
function a grab_left(b value)
   provisos(Bits#(a, sa), Bits#(b, sb), Add#(x, sa, sb));

   let result = truncate(pack(value) >> fromInteger((valueOf(sb) - valueOf(sa))));

   return unpack(result);
endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function a reverse_bytes (a value)
      provisos (Bits#(a, sa), Add#(8, ignore, sa), Add#(8, sa, sb));

      Bit#(sa) result_bits = 0;
      Bit#(sa) value_bits = pack(value);
      Bit#(8)  one_byte = 0;
      Bit#(sb) z = 0;

      //for (Integer x = (valueOf(sa) - 1); x > 0; x = x - 8)
      for (Integer xx = 0; xx < valueOf(sa); xx = xx + 8)
	 begin
	    Integer x = xx - (valueOf(sa) - 1);
	    Nat y = fromInteger(x);
	    one_byte = value_bits[y:(y - 7)];
	    z = {one_byte, result_bits};
	    result_bits = grab_left(z);
	 end

      return unpack(result_bits);

endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Integer getSizeOf(a value)
   provisos(Bits#(a, sa));
   return valueOf(sa);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bit#(m) zExtend(Bit#(n) value)
   provisos(Add#(n,m,k));
   Bit#(k) out = zeroExtend(value);
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueOf(m) - 1:0];
endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bit#(m) sExtend(Bit#(n) value)
   provisos(Add#(n,m,k));
   Bit#(k) out = signExtend(value);
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueOf(m) - 1:0];
endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function a cExtend(b value)
   provisos(Bits#(a, sa), Bits#(b, sb));

   let out = unpack(zExtend(pack(value)));

   return out;
endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bit#(m) zExtendLSB(Bit#(n) value)
   provisos( Add#(n,m,k) );
   Bit#(k) out = { value, 0 };
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueof(k)-1:valueof(n)];
endfunction

`ifdef BSVTOKAMI
(* nogen *)
`endif
function a cExtendLSB(b value)
   provisos( Bits#(a,sa), Bits#(b,sb) );
   let out = unpack(zExtendLSB(pack(value)));
   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bit#(size) getIndex (Vector#(count, Bool) vector)
   provisos (Log#(count, size));

   let icount = valueOf(count);

   Integer selected = 0;

   for (Integer x = 0; x < icount; x = x + 1)
      if (vector[x]) selected = x;

   return fromInteger(selected);
endfunction


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Action dummyAction ();
   action
      $write("");
   endaction
endfunction


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef Bit#(TLog#(TAdd#(m, 1)))  LBit#(numeric type m);

`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef UInt#(TLog#(TAdd#(m, 1))) LUInt#(numeric type m);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bit#(m) duplicate(Bit#(n) d) provisos(Mul#(n,x,m));
   function Bit#(n) setVal(Integer i) = d;
   Vector#(x,Bit#(n)) v = map(setVal, genVector);
   return pack(v);
endfunction


endpackage
