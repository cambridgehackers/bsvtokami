
import Foo::*;
export Foo::*;
export Bar(..);

interface Reg#(type a);
    method Action _write(a v);
    method a _read();
endinterface

typedef union tagged {
  a Valid;
  void Invalid;
} Maybe#(type a);

module mkReg#(a dv)(Reg#(a));
endmodule

module mkMyTest(Empty);
    Reg#(Maybe#(Bit#(12))) x <- mkReg(0);
    Bit#(12) a = 17;
    rule doDecrementEven if (a == x &&& a matches 17);
    	 x <= Valid(a-1);
	 $display(x);
    endrule
endmodule
