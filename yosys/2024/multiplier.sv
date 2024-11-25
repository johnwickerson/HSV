// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
		   input 	 rst,
                   input 	 clk,
                   input [7:0] 	 in1,
                   input [7:0] 	 in2,
                   output [15:0] out
                  );
   reg [3:0]  stage = 0;
   reg [15:0] accumulator = 0;
   reg [7:0]  in1_shifted = 0;
   reg [15:0] in2_shifted = 0;


   // Logic for controlling the stage
   always @(posedge clk) 
     if (rst || stage == 9)
       stage <= 0;
     else
       stage <= stage + 1;
   
   // Logic for in1_shifted and in2_shifted
   always @(posedge clk) 
     if (rst) begin
	in1_shifted <= 0;
	in2_shifted <= 0;
     end else if (stage == 0) begin
        in1_shifted <= in1;
        in2_shifted <= in2;
     end else begin
        in1_shifted <= in1_shifted >> 1;
        in2_shifted <= in2_shifted << 1;
     end

   // Logic for the accumulator
   always @(posedge clk)
     if (rst || stage == 9) begin
	accumulator <= 0;
     end else if (in1_shifted[0]) begin
        accumulator <= accumulator + in2_shifted;
     end

   // Output logic
   assign out = accumulator;


`ifdef FORMAL

   always @(posedge clk) begin

     // write your properties here!

   end

`endif
   
   
endmodule
