
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
   Reg#(Bit#(32)) data <- mkReg(32'd0);
   rule produce;
      consumer.send(data);
      data <= data + 32'd1;
   endrule

endmodule

module mkProducerConsumer#(ExtCall ext)(Producer);
   Consumer consumer <- mkConsumer(ext);
   Reg#(Bit#(32)) data <- mkReg(32'd0);
   rule produce;
      consumer.send(data);
      data <= data + 32'd1;
   endrule

endmodule

module mkProduceConsume#(ExtCall extpc)(Foo);
   Reg#(Bit#(32)) data <- mkReg(32'd0);
   rule produce;
      extpc.extCall(data);
      data <= data + 32'd1;
   endrule
endmodule
