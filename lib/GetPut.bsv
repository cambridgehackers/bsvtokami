package GetPut;

import FIFO::*;
import FIFOF::*;

interface Get#(type a);
   method ActionValue#(a) get();
endinterface

interface Put#(type a);
   method Action put(a v);
endinterface

typeclass ToGet#(type a, type b);
   function Get#(b) toGet(a ax);
endtypeclass

typeclass ToPut#(type a, type b);
   function Put#(b) toPut(a ax);
endtypeclass

instance ToGet#(Get#(a), a);
   function Get#(a) toGet(Get#(a) g);
      return g;
   endfunction
endinstance

instance ToPut#(Put#(a), a);
   function Put#(a) toPut(Put#(a) g);
      return g;
   endfunction
endinstance

instance ToGet#(FIFO#(a), a);
   function Get#(a) toGet(FIFO#(a) fifo);
      return (interface Get#(a);
		 method ActionValue#(a) get();
		    fifo.deq();
		    return fifo.first();
		 endmethod
	      endinterface);
   endfunction
endinstance

instance ToPut#(FIFO#(a), a);
   function Put#(a) toPut(FIFO#(a) fifo);
      return (interface Put#(a);
		 method Action put(a v);
		    fifo.enq(v);
		 endmethod
	      endinterface);
   endfunction
endinstance

instance ToGet#(FIFOF#(a), a);
   function Get#(a) toGet(FIFOF#(a) fifof);
      return (interface Get#(a);
		 method ActionValue#(a) get();
		    fifof.deq();
		    return fifof.first();
		 endmethod
	      endinterface);
   endfunction
endinstance

instance ToPut#(FIFOF#(a), a);
   function Put#(a) toPut(FIFOF#(a) fifof);
      return (interface Put#(a);
		 method Action put(a v);
		    fifof.enq(v);
		 endmethod
	      endinterface);
   endfunction
endinstance

endpackage
