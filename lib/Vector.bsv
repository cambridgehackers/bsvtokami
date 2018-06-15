package Vector;

interface Vector#(numeric type len, type element_type);
endinterface

typeclass VectorOps#(type index_type);
   function Vector#(len, element_type) \$vecnew (Integer size);
   function Vector#(len, element_type) \$vecupdate (Vector#(len, element_type) vector, index_type offset, element_type v);
   function element_type \$vecselect (Vector#(len, element_type) vector, index_type offset);

   function Vector#(len, element_type) update(Vector#(len, element_type) vector, index_type offset, element_type v);
   function element_type select(Vector#(len, element_type) vector, index_type offset);
 endtypeclass

(* nogen *)
function Vector#(len, element_type) genWith(function element_type func(Integer xi));
   function Vector#(len, element_type) genWithRec(Vector#(len, element_type) vect, Integer i);
       if (i < valueOf(len))
	  return genWithRec($vecupdate(vect, i, func(i)), i + 1);
       else
	  return vect;
   endfunction
   return genWithRec($vecnew(valueOf(len)), 0);
endfunction

(* nogen *)
function Vector#(len, element_type) newVector();
   function element_type elt(Integer xi); return ?; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, Integer) genVector();
   function Integer elt(Integer xi); return xi; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) replicate(element_type v);
   function element_type elt(Integer xi); return v; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len_plus_1, element_type) cons(element_type v, Vector#(len, element_type) vect)
   provisos (Add#(len, 1, len_plus_1));
   function element_type elt(Integer xi); if (xi == 0) return v; else return vect[xi - 1]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(0, element_type) nil(); return newVector(); endfunction

(* nogen *)
function Vector#(vsize, element_type) append(Vector#(lena, element_type) vecta, Vector#(lenb, element_type) vectb)
   provisos (Add#(lena, lenb, vsize));
   function element_type elt(Integer xi); if (xi < valueOf(lena) ) return vecta[xi]; else return vectb[xi - valueOf(lena)]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(vsize, element_type) concat(Vector#(m, Vector#(n, element_type)) vectofvects)
   provisos (Mul#(m, n, vsize));
   function element_type elt(Integer xi);
      Integer vectnum = xi / valueOf(n);
      Integer eltnum = xi % valueOf(n);
      return vectofvects[vectnum][eltnum];
   endfunction
   return genWith(elt);
endfunction

(* nogen *)
function element_type head(Vector#(len, element_type) v)
   provisos (Add#(1, a__, len));
   return v[0];
endfunction

(* nogen *)
function element_type tail(Vector#(len, element_type) v)
   provisos (Add#(1, a__, len));
   return v[valueOf(len) - 1];
endfunction

(* nogen *)
function Vector#(vsize, element_type) init(Vector#(vsize1, element_type) v)
   provisos (Add#(vsize, 1, vsize1));
   function element_type elt(Integer xi); return v[xi]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(vsize, element_type) take(Vector#(vsize1, element_type) v)
   provisos (Add#(vsize, a__, vsize1));
   function element_type elt(Integer xi); return v[xi]; endfunction
   return genWith(elt);
endfunction

// deprecated
(* nogen *)
function Vector#(vsize, element_type) drop(Vector#(vsize1, element_type) v)
   provisos (Add#(vsize, a__, vsize1));
   function element_type elt(Integer xi); return v[xi + valueOf(vsize1) - valueOf(vsize)]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(vsize, element_type) takeTail(Vector#(vsize1, element_type) v)
   provisos (Add#(vsize, a__, vsize1));
   function element_type elt(Integer xi); return v[xi + valueOf(vsize1) - valueOf(vsize)]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(vsize, element_type) takeAt(Integer startPos, Vector#(vsize1, element_type) vect)
   provisos (Add#(vsize, a__, vsize1));
   function element_type elt(Integer xi); return vect[xi - startPos]; endfunction
   return genWith(elt);
endfunction

// Mapping Functions over Vectors

(* nogen *)
function Vector#(vsize,b_type) map(function b_type func(a_type x),
				   Vector#(vsize, a_type) vect);
   function b_type funci(Integer i);
      return func(vect[i]);
   endfunction
   return genWith(funci);
endfunction

// Vector to Vector Functions

(* nogen *)
function Vector#(len, element_type) rotate(Vector#(len, element_type) vect);
   function element_type elt(Integer xi); return vect[(xi + 1) % valueOf(len) ]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) rotateR(Vector#(len, element_type) vect);
   function element_type elt(Integer xi); return vect[(xi - 1) % valueOf(len) ]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) rotateBy(Vector#(len, element_type) vect, Integer n);
   function element_type elt(Integer xi); return vect[(xi + n) % valueOf(len) ]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) shiftInAt0(Vector#(len, element_type) vect, element_type new_elt);
   function element_type elt(Integer xi);
      if (xi == 0)
	 return new_elt;
      else
	 return vect[xi - 1]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) shiftInAtN(Vector#(len, element_type) vect, element_type new_elt);
   function element_type elt(Integer xi);
      if (xi == valueOf(len) - 1)
	 return new_elt;
      else
	 return vect[xi + 1]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) shiftOutFrom0(element_type new_elt, Vector#(len, element_type) vect, Integer amount);
   function element_type elt(Integer xi);
      if (xi >= valueOf(len) - amount)
	 return new_elt;
      else
	 return vect[xi + amount]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) shiftOutFromN(element_type new_elt, Vector#(len, element_type) vect, Integer amount);
   function element_type elt(Integer xi);
      if (xi < amount)
	 return new_elt;
      else
	 return vect[xi - amount]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(len, element_type) reverse(Vector#(len, element_type) vect);
   function element_type elt(Integer xi);
      return vect[valueOf(len) - xi - 1]; endfunction
   return genWith(elt);
endfunction

(* nogen *)
function Vector#(m, Vector#(n, element_type)) transpose(Vector#(m, Vector#(n, element_type)) vectofvects);
   function Vector#(n, element_type) outer_elt(Integer xi);
(* nogen *)
      function element_type inner_elt(Integer yi);
	 return vectofvects[yi][xi];
      endfunction
      return genWith(inner_elt);
   endfunction
   return genWith(outer_elt);
endfunction

// Fold Functions
(* nogen *)
function b_type foldr(function b_type func(a_type x, b_type y),
		       b_type seed, Vector#(vsize,a_type) vect);
   function b_type foldrec(Integer i, b_type v);
      if (i < valueOf(vsize))
	 return foldrec(i + 1, func(vect[valueOf(vsize) - i - 1], v));
      else
	 return v;
   endfunction
   return foldrec(0, seed);
endfunction

(* nogen *)
function b_type foldl(function b_type func(b_type y, a_type x),
                       b_type seed, Vector#(vsize,a_type) vect);
   b_type result = seed;
   function b_type foldrec(Integer i, b_type v);
      if (i < valueOf(vsize))
	 return foldrec(i + 1, func(v, vect[i]));
      else
	 return v;
   endfunction
   return foldrec(0, seed);
endfunction

(* nogen *)
function a_type fold(function b_type func(a_type y, a_type x),
		      Vector#(vsize,a_type) vect);
   function b_type recursive(Integer lb, Integer rb);
       if (lb == rb)
	  return vect[lb];
       else if (lb == rb - 1)
	  return func(vect[lb], vect[rb]);
       else begin
	  Integer midpoint = lb + (rb - lb + 1 / 2);
	  a_type v0 = recursive(lb, lb + midpoint);
	  a_type v1 = recursive(lb + midpoint, rb);
	  return func(v0, v2);
       end
   endfunction
   return recursive(0, valueOf(vsize)-1, seed);
endfunction

(* nogen *)
function a_type foldr1(function a_type func(a_type x, a_type y),
                      Vector#(vsize,a_type) vect)
   provisos (Add#(vsizem1, 1, vsize));
   Vector#(vsizem1, a_type) subvec = take(vect);
   return foldr(func, tail(vect), subvec);
endfunction

(* nogen *)
function a_type foldl1(function a_type func(a_type y, a_type x),
                      Vector#(vsize,a_type) vect)
   provisos (Add#(vsizem1, 1, vsize));
   Vector#(vsizem1, a_type) subvec = takeTail(vect);
   return foldl(func, head(vect), subvec);
endfunction

// Tests on Vectors

(* nogen *)
function Bool elem (element_type needle,
                    Vector#(vsize,element_type) vect )
  provisos (Eq#(element_type));
   function Bool found(Bool f, element_type elt);
      return f || (elt == needle);
   endfunction
   return foldl(found, False, vect);
endfunction

(* nogen *)
function Bool any(function Bool pred(element_type x1),
                  Vector#(vsize,element_type) vect );
   function Bool anypred(Bool f, element_type elt);
      return f || pred(elt);
   endfunction
   return foldl(anypred, False, vect);
endfunction

(* nogen *)
function Bool all(function Bool pred(element_type x1),
                  Vector#(vsize,element_type) vect );
   function Bool allelts(Bool f, element_type elt);
      return f && pred(elt);
   endfunction
   return foldl(allelts, True, vect);
endfunction

(* nogen *)
function Bool vector (Vector#(vsize, Bool) vect );
   function Bool anyelt(Bool f, Bool g);
      return f || g;
   endfunction
   return foldl(anyelt, False, vect);
endfunction

(* nogen *)
function Bool vectand (Vector#(vsize, Bool) vect );
   function Bool allelts(Bool f, Bool g);
      return f && g;
   endfunction
   return foldl(allelts, False, vect);
endfunction

(* nogen *)
function UInt#(logv1) countElem (element_type needle,
                                 Vector#(vsize, element_type) vect)
  provisos (Eq#(element_type), Add#(vsize, 1, vsize1),
            Log#(vsize1, logv1));
   
   function UInt#(logv1) countelt(UInt#(logv1) sum, element_type elt);
      return sum + ((needle == elt) ? 1 : 0);
   endfunction
   return foldl(countelt, 0, vect);
endfunction

(* nogen *)
function UInt#(logv1) countIf (function Bool pred(element_type x1),
                               Vector#(vsize, element_type) vect)
  provisos (Add#(vsize, 1, vsize1), Log#(vsize1, logv1));
   
   function UInt#(logv1) countelt(UInt#(logv1) sum, element_type elt);
      return sum + (pred(elt) ? 1 : 0);
   endfunction
   return foldl(countelt, 0, vect);
endfunction

(* nogen *)
function Maybe#(element_type) find (function Bool pred(element_type x),
				    Vector#(vsize, element_type) vect);

   function Maybe#(element_type) findelt(Maybe#(element_type) found, element_type elt);
     case (found) matches
	tagged Invalid: return pred(elt) ? Valid(elt) : Invalid;
	tagged Valid .x: return found;
     endcase
   endfunction
   return foldl(findelt, Invalid, vect);
endfunction

(* nogen *)
function Maybe#(UInt#(logv)) findElem (element_type needle,
				       Vector#(vsize, element_type) vect)
  provisos (Eq#(element_type)
	    , Add#(xx1, 1, vsize)
            , Log#(vsize, logv));
   
   function Maybe#(UInt#(logv)) findelt(Maybe#(UInt#(logv)) found, Integer i);
     case (found) matches
	tagged Invalid: return (vect[i] == needle) ? Valid(fromInteger(i)) : Invalid;
	tagged Valid .x: return found;
     endcase
   endfunction
   Vector#(vsize, Integer) indices = genVector();
   return foldl(findelt, Invalid, indices);
endfunction

(* nogen *)
function Maybe#(UInt#(logv)) findIndex(function Bool pred(element_type x1),
				       Vector#(vsize, element_type) vect)
   provisos (Add#(xx1,1,vsize), Log#(vsize, logv));
   
   function Maybe#(UInt#(logv)) findelt(Maybe#(UInt#(logv)) found, Integer i);
     case (found) matches
	tagged Invalid: return pred(vect[i]) ? Valid(fromInteger(i)) : Invalid;
	tagged Valid .x: return found;
     endcase
   endfunction
   Vector#(vsize, Integer) indices = genVector();
   return foldl(findelt, Invalid, indices);
endfunction

// Bit-Vector Operations

(* nogen *)
function Bit#(n) rotateBitsBy (Bit#(n) bvect, UInt#(logn) rotatebits)
  provisos (Log#(n,logn), Add#(1,xxx,n));
   
   Vector#(n, Bit#(1)) bits = unpack(bvect);
   function Bit#(1) elt(Integer xi); return bits[(fromInteger(xi) + rotatebits) % fromInteger(valueOf(n)) ]; endfunction
   Vector#(n, Bit#(1)) rotated = genWith(elt);
   return pack(rotated);
endfunction

(* nogen *)
function UInt#(logn1) countOnesAlt (Bit#(n) bvect)
   provisos (Add#(1,n,n1), Log#(n1,logn1));
   Vector#(n, Bit#(1)) bits = unpack(bvect);
   function UInt#(logn1) countone(UInt#(logn1) sum, Bit#(1) b);
      return sum + ((b == 1) ? 1 : 0);
   endfunction
   return foldl(countone, 0, bits);
endfunction

// Functions on Vectors of Registers

(* nogen *)
function Vector#(n,a) readVReg ( Vector#(n, Reg#(a)) vrin) ;
   function a readreg(Reg#(a) r); return r; endfunction
   return map(readreg, vrin);
endfunction

(* nogen *)
function Action writeVReg ( Vector#(n, Reg#(a)) vr,
                            Vector#(n,a) vdin) ;
   action
      function Action loop(Integer i);
	 action
	    if (i < valueOf(n)) begin
	       vr[i] <= vdin[i];
	       loop(i + 1);
	    end
	 endaction
      endfunction
      loop(0);
   endaction
endfunction

// Combining Vectors with Zip

(* nogen *)
function Vector#(vsize,Tuple2 #(a_type, b_type))
      zip( Vector#(vsize, a_type) vecta,
           Vector#(vsize, b_type) vectb);
   
   function Tuple2#(a_type, b_type) combine(Integer i);
      return tuple2(vecta[i], vectb[i]);
   endfunction
   return genWith(combine);
endfunction

(* nogen *)
function Vector#(vsize,Tuple3 #(a_type, b_type, c_type))
      zip3(Vector#(vsize, a_type) vecta,
	   Vector#(vsize, b_type) vectb,
	   Vector#(vsize, c_type) vectc);
   
   function Tuple3#(a_type, b_type, c_type) combine(Integer i);
      return tuple3(vecta[i], vectb[i], vectc[i]);
   endfunction
   return genWith(combine);
endfunction

(* nogen *)
function Vector#(vsize,Tuple4 #(a_type, b_type, c_type, d_type))
      zip4(Vector#(vsize, a_type) vecta,
	   Vector#(vsize, b_type) vectb,
	   Vector#(vsize, c_type) vectc,
	   Vector#(vsize, d_type) vectd);
   
   function Tuple4#(a_type, b_type, c_type, d_type) combine(Integer i);
      return tuple4(vecta[i], vectb[i], vectc[i], vectd[i]);
   endfunction
   return genWith(combine);
endfunction

(* nogen *)
function Vector#(vsize,Tuple2 #(a_type, b_type))
      zipAny(Vector#(m,a_type) vect1,
             Vector#(n,b_type) vect2)
  provisos (Max#(m,vsize,m),
	    Max#(n, vsize, n),
	    Add#(vsize, a__, m),
	    Add#(vsize, b__, n));
   Vector#(vsize, a_type) as = take(vect1);
   Vector#(vsize, b_type) bs = take(vect2);
   return zip(as, bs);
endfunction

(* nogen *)
function Tuple2#(Vector#(vsize,a_type), Vector#(vsize, b_type))
      unzip(Vector#(vsize,Tuple2 #(a_type, b_type)) vectab);
   return tuple2(map(tpl_1, vectab), map(tpl_2, vectab));
endfunction

// ZipWith Functions

(* nogen *)
function Vector#(vsize,c_type)
         zipWith (function c_type func(a_type x, b_type y),
                  Vector#(vsize,a_type) vecta,
                  Vector#(vsize,b_type) vectb );
   function c_type funci(Integer i);
      return func(vecta[i], vectb[i]);
   endfunction
   return genWith(funci);
endfunction

(* nogen *)
function Vector#(vsize,c_type)
         zipWithAny (function c_type func(a_type x, b_type y),
                      Vector#(m,a_type) vecta,
                      Vector#(n,b_type) vectb )
  provisos (Max#(n, vsize, n), Max#(m, vsize, m));

   function c_type funci(Integer i);
      return func(vecta[i], vectb[i]);
   endfunction
   return genWith(funci);
endfunction

(* nogen *)
function Vector#(vsize,d_type)
        zipWith3(function d_type func(a_type x, b_type y, c_type z),
                 Vector#(vsize,a_type) vecta,
                 Vector#(vsize,b_type) vectb,
                 Vector#(vsize,c_type) vectc );
   
   function d_type funci(Integer i);
      return func(vecta[i], vectb[i], vectc[i]);
   endfunction
   return genWith(funci);
endfunction

(* nogen *)
function Vector#(vsize,d_type)
   zipWithAny3(function d_type func(a_type x, b_type y, c_type z),
               Vector#(m,a_type) vecta,
               Vector#(n,b_type) vectb,
               Vector#(o,c_type) vectc )
   provisos (Max#(n, vsize, n), Max#(m, vsize, m), Max#(o, vsize, o));
   
   function d_type funci(Integer i);
      return func(vecta[i], vectb[i], vectc[i]);
   endfunction
   return genWith(funci);
endfunction
// Monadic Operations

(* nogen *)
function m#(Vector#(vsize, element_type)) genWithM(function m#(element_type) func(Integer x))
   provisos (Monad#(m));
   Vector#(vsize, Integer) indices = genVector;
   Vector#(vsize, element_type) result = newVector;

   function m#(Vector#(vsize, element_type)) upd(element_type elt);
      Integer i = 0;
      //return \return (update(result, i, elt));
   endfunction

   //return \return (result);
endfunction

(* nogen *)
function m#(Vector#(vsize, b_type)) mapM( function m#(b_type) func(a_type x),
					 Vector#(vsize, a_type) vecta )
   provisos (Monad#(m));
   function m#(b_type) gen_elt(Integer i);
      m#(b_type) v = func(vecta[i]);
      return v;
   endfunction
   return genWithM(gen_elt);
endfunction

(* nogen *)
function m#(void) mapM_( function m#(b_type) func(a_type x),
			Vector#(vsize, a_type) vecta )
   provisos (Monad#(m));
   function m#(b_type) gen_elt(Integer i);
      m#(b_type) v = func(vecta[i]);
      return v;
   endfunction
   let vect = genWithM(gen_elt);
   return ?;
endfunction

(* nogen *)
function m#(Vector#(vsize, c_type)) zipWithM( function m#(c_type) func(a_type x, b_type y),
					     Vector#(vsize, a_type) vecta,
					     Vector#(vsize, b_type) vectb )
  provisos (Monad#(m));
   function m#(c_type) gen_elt(Integer i);
      m#(c_type) v = func(vecta[i], vectb[i]);
      return v;
   endfunction
   return genWithM(gen_elt);
endfunction

(* nogen *)
function m#(void) zipWithM_( function m#(c_type) func(a_type x, b_type y),
			    Vector#(vsize, a_type) vecta,
			    Vector#(vsize, b_type) vectb )
  provisos (Monad#(m));
   function m#(c_type) gen_elt(Integer i);
      m#(c_type) v = func(vecta[i], vectb[i]);
      return v;
   endfunction
   m#(Vector#(vsize, c_type)) vect = genWithM(gen_elt);
   return ?;
endfunction

(* nogen *)
function m#(Vector#(vsize, d_type)) zipWith3M( function m#(d_type) func(a_type x, b_type y, c_type z),
					      Vector#(vsize, a_type) vecta,
					      Vector#(vsize, b_type) vectb,
					      Vector#(vsize, c_type) vectc )
   provisos (Monad#(m));
   function m#(d_type) gen_elt_3m(Integer i);
      m#(d_type) v = func(vecta[i], vectb[i], vectc[i]);
      return v;
   endfunction
   return genWithM(gen_elt_3m);
endfunction

(* nogen *)
function m#(Vector#(vsize, b_type)) replicateM( m#(b_type) c)
   provisos (Monad#(m));
   function m#(b_type) gen_elt(Integer i);
      return c;
   endfunction
   return genWithM(gen_elt);
endfunction

endpackage
