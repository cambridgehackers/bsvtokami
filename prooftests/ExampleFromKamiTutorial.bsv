
// should be in Prelude.bsv
interface Foo;
endinterface

interface Consumer;
   method Action send(Bit#(32) v);
endinterface

interface Producer;
endinterface

interface ExtCall;
   method Action extCall(Bit#(32) v);
endinterface

module mkExtCall(ExtCall);
   method Action extCall(Bit#(32) v);
   endmethod
endmodule

module mkConsumer#(ExtCall ext)(Consumer);
   method Action send(Bit#(32) v);
      ext.extCall(v);
   endmethod
endmodule

module mkProducer#(Consumer consumer)(Producer);
   Bit#(32) initval = 32'd0;
   Reg#(Bit#(32)) data <- mkReg(initval);
   rule produce;
      consumer.send(data);
      data <= data + 1;
   endrule

endmodule

module mkProduceConsume#(ExtCall extpc)(Foo);
   Bit#(32) initval = 32'd0;
   Reg#(Bit#(32)) data <- mkReg(initval);
   rule produce_consume;
      extpc.extCall(data);
      data <= data + 1;
   endrule
endmodule
