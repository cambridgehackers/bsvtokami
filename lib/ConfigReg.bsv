package ConfigReg;

(* nogen *)
module mkConfigReg#(data_t v)(Reg#(data_t)) provisos (Bits#(data_t));
    method Action _write(data_t v);
    endmethod
endmodule

endpackage
