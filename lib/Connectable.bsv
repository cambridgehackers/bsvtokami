package Connectable;
import GetPut::*;

typeclass Connectable#(type a, type b);
    module mkConnection#(a x1, b x2)(Empty);
endtypeclass

instance Connectable#(Get#(a), Put#(a));
   module mkConnection#(Get#(a) g, Put#(a) p)(Empty);
      rule getput;
	 let v <- g.get();
	 p.put(v);
      endrule
   endmodule
endinstance

// instance Connectable#(Tuple2#(a1, a2), Tuple2#(b1, b2))
//    provisos (Connectable#(a1, b1), Connectable#(a2, b2));
//    module mkConnection#(Tuple2#(a1, a2) x, Tuple2#(b1, b2) y)(Empty);
//       mkConnection(tpl_1(x), tpl_2(y));
//       mkConnection(tpl_2(x), tpl_2(y));
//    endmodule
// endinstance

// instance Connectable#(Vector#(n, a), Vector#(n, b))
//   provisos (Connectable#(a, b));
// ...
// endinstance

// instance Connectable#(ListN#(n, a), ListN#(n, b))
//    provisos (Connectable#(a, b));
// endinstance

instance Connectable#(ActionValue#(a), function Action f(a x));
   module mkConnection#(ActionValue#(a) y, function Action f(a x))(Empty);
      rule connect;
	 let v <- y();
	 f(v);
      endrule
   endmodule
endinstance

instance Connectable#(function Action f(a x), ActionValue#(a));
   module mkConnection#(function Action f(a x), ActionValue#(a) y)(Empty);
      rule connect;
	 let v <- y();
	 f(v);
      endrule
   endmodule
endinstance

instance Connectable#(a, function Action f(a x));
   module mkConnection#(a x, function Action f(a y))(Empty);
      rule connect;
	 f(x);
      endrule
   endmodule
endinstance

instance Connectable#(function Action f(a x), a);
   module mkConnection#(function Action f(a y), a x)(Empty);
      rule connect;
	 f(x);
      endrule
   endmodule
endinstance

// instance Connectable#(Inout#(a, x1), Inout#(a, x2))
//    provisos (Bit#(a,sa));

// endinstance
