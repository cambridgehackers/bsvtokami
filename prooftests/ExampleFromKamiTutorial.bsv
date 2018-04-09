
interface Consumer;
   method Action send(Bit#(32) v);
endinterface

interface Producer;
endinterface

`ifdef EXTCALL
function Action extCall(Bit#(32) v);
   // something
endfunction
`endif

module mkConsumer(Consumer);
   method Action send(Bit#(32) v);
      //extCall(data);
   endmethod
endmodule

module mkProducer#(Consumer consumer)(Producer);
   Reg#(Bit#(32)) data <- mkReg(0);
   rule produce;
      consumer.send(data);
      data <= data + 1;
   endrule

endmodule

module mkProduceConsume(Empty);
   Reg#(Bit#(32)) data <- mkReg(0);
   rule produce_consume;
      //extCall(data);
      data <= data + 1;
   endrule
endmodule
