
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

module mkProducer#(Consumer consumer, Integer numRules)(Producer);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Reg#(Bit#(32)) datafoo <- mkReg(0);
      rule produce;
	 consumer.send(datafoo);
	 datafoo <= datafoo + 10;
      endrule
   end
endmodule

module mkProduceConsume#(ExtCall extpc, Integer numRules)(Empty);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Reg#(Bit#(32)) data <- mkReg(0);
      rule produce;
	 data <= data + 10;
         extpc.extCall(data);
      endrule
   end
endmodule
