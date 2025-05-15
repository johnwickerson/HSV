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

   reg [7:0]  in1_latched;
   reg [7:0]  in2_latched;

   // Latching the inputs (not part of the implementation, just the proof)
   always @(posedge clk)
     if (stage == 0) begin
	in1_latched <= in1;
	in2_latched <= in2;
     end
   
   always @(posedge clk) begin

      // Question 1
      output_upper_bound:
	assert property (out < 16'd65026); 
        // Could also be written as 16'hFE02 or 16'b1111111000000010

      // Question 2
      stage_increments: 
	assert property (disable iff (rst) 
			 1 |=> stage == ($past(stage) + 1) % 10);
	// Stage increments at each posedge, modulo 10. 
	// (We need the "1" above so that $past is well defined.)

      // Question 3
      result_inputs: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##9 out == $past(in1, 9) * $past(in2, 9));
	// Alternatively: `out = in1_latched * in2_latched`.

      // Question 4	 
      output_monotonic: 
	assert property (stage > 0 |-> (out >= $past(out)));

      // Question 5
      intermediate_results_5: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##5 accumulator == $past(in2, 5) * $past(in1[3:0], 5));
	// Alternatively: `accumulator == in2_latched * in1_latched[3:0]`

      // Question 6
      intermediate_results_1:
	assert property (stage == 0 |-> ##1 accumulator == 0);

      intermediate_results_2: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##2 accumulator == $past(in2, 2) * $past(in1[0:0], 2));
	 
      intermediate_results_3: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##3 accumulator == $past(in2, 3) * $past(in1[1:0], 3));
	 
      intermediate_results_4: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##4 accumulator == $past(in2, 4) * $past(in1[2:0], 4));
	 
      intermediate_results_6: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##6 accumulator == $past(in2, 6) * $past(in1[4:0], 6));
	 
      intermediate_results_7: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##7 accumulator == $past(in2, 7) * $past(in1[5:0], 7));
	 
      intermediate_results_8: 
	assert property (disable iff (rst) 
			 stage == 0 |-> ##8 accumulator == $past(in2, 8) * $past(in1[6:0], 8));

      // Question 7
      in1_shifted_is_in1_shifted_right: 
	assert property (in1_shifted == (in1_latched >> (stage - 4'b1)));

      // Question 8
      in2_shifted_is_in2_shifted_left:
	assert property (stage > 0 |-> in2_shifted == (in2_latched << (stage - 4'b1)));

      // Question 9
      prime_13:
	cover ((stage == 9) && (out == 16'd13) && (($past(in1,9) == 1) == ($past(in2,9) == 1)));

      // Question 10
      intermediate_results_N: 
	assert property (disable iff (rst) 
			 accumulator == (stage == 0 ? 0 : in2_latched * (in1_latched & ((1<<(stage - 4'b1)))-1)));


	
   end

`endif
   
endmodule
