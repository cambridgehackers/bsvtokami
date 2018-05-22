package RegFile;

interface RegFile #(type index_t, type data_t);
    method Action upd(index_t addr, data_t d);
    method data_t sub(index_t addr);
endinterface: RegFile

(* nogen *)
module mkRegFile#( index_t lo_index, index_t hi_index )
                 ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t,  size_data));
endmodule

(* nogen *)
module mkRegFileFull( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data),
            Bounded#(index_t) );
endmodule

(* nogen *)
module mkRegFileWCF#( index_t lo_index, index_t hi_index )
                    ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t,  size_data));
   
endmodule

(* nogen *)
module mkRegFileLoad#
           ( String file, index_t lo_index, index_t hi_index)
           ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data));
   
endmodule

(* nogen *)
module mkRegFileFullLoad#( String file)
                         ( RegFile#(index_t, data_t))
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data),
            Bounded#(index_t) );
endmodule

(* nogen *)
module mkRegFileWCFLoad#
           ( String file, index_t lo_index, index_t hi_index)
           ( RegFile#(index_t, data_t) )
  provisos (Bits#(index_t, size_index),
            Bits#(data_t, size_data));
   
endmodule

endpackage
