interface Empty;
endinterface

interface SubConsumer;
   method Acton foo();
endinterface

interface Consumer;
   method Action send(Bit#(32) v);
   //interface SubConsumer sc;
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

`ifdef FOR_LOOPS
module mkProducer#(Consumer consumer, Integer numRules)(Producer);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Bit#(32) initval = 32'd0;
      Reg#(Bit#(32)) datafoo <- mkReg(initval);
      rule produce;
	 consumer.send(datafoo);
	 datafoo <= datafoo + 10;
      endrule
   end
endmodule

`ifdef ManyConsumer
module mkManyConsumer#(ExtCall ext, Integer numRules)(Producer);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Consumer c <- mkConsumer(ext);
      Bit#(32) initval = 32'd0;
      Reg#(Bit#(32)) datafoo <- mkReg(initval);
      rule produce;
	 c.send(datafoo);
	 datafoo <= datafoo + 10;
      endrule
   end
endmodule
`endif

`ifdef ProducerConsumer
module mkProducerConsumer#(ExtCall ext, Integer numRules)(Producer);
   Consumer c0 <- mkConsumer(ext);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Bit#(32) initval = 32'd0;
      Reg#(Bit#(32)) datafoo <- mkReg(initval);
      rule produce;
	 c0.send(datafoo);
	 datafoo <= datafoo + 10;
      endrule
   end
endmodule
`endif

module mkProduceConsume#(ExtCall extpc, Integer numRules)(Empty);
   for (Integer i = 0; i < numRules; i = i + 1) begin
      Bit#(32) initval = 32'd0;
      Reg#(Bit#(32)) data <- mkReg(initval);
      rule produce;
	 data <= data + 10;
         extpc.extCall(data);
      endrule
   end
endmodule
`endif // FOR_LOOPS