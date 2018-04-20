
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

module mkProducer#(Consumer consumer, Integer numRegs)(Producer);
   for (Integer i = 0; i < numRegs; numRegs = numRegs + 1) begin
      Reg#(Bit#(32)) data <- mkReg(0);
      rule produce;
	 consumer.send(data);
	 data <= data + fromInteger(numRegs);
      endrule
   end
endmodule

module mkProduceConsume#(ExtCall extpc)(Empty);
   for (Integer i = 0; i < numRegs; numRegs = numRegs + 1) begin
      Reg#(Bit#(32)) data <- mkReg(0);
      rule produce;
	 consumer.send(data);
	 data <= data + fromInteger(numRegs);
         extpc.extCall(data);
      endrule
   end
endmodule
