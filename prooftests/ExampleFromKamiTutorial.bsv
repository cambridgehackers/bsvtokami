
// should be in Prelude.bsv
interface Empty;
endinterface

interface Consumer;
   method Action send(Bit#(32) v);
endinterface

interface Producer;
endinterface

interface ExtCall;
   method Action extCall(Bit#(32) v);
endinterface

module mkConsumer#(ExtCall ext)(Consumer);
   method Action send(Bit#(32) v);
      ext.extCall(v);
   endmethod
endmodule

module mkProducer#(Consumer consumer)(Producer);
   Reg#(Bit#(32)) data <- mkReg(0);
   rule produce;
      consumer.send(data);
      data <= data + 1;
   endrule

endmodule

module mkProduceConsume#(ExtCall extpc)(Empty);
   Reg#(Bit#(32)) data <- mkReg(0);
   rule produce_consume;
      extpc.extCall(data);
      data <= data + 1;
   endrule
endmodule
