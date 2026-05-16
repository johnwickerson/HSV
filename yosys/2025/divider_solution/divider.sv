module divider (          // 5-bit unsigned integer divider
  input            clk,   // clock
  input            rst,   // reset
  input            go,    // start calculation
  input [4:0]      num,   // input: numerator
  input [4:0]      den,   // input: denominator
  output [4:0]     rem,   // result: remainder
  output reg [4:0] quo,   // result: quotient
  output reg       busy,  // calculation in progress
  output reg       done,  // calculation is complete
  output reg       valid, // result is valid
  output reg       dbz    // divide-by-zero detected!
);

  reg [4:0] den_latched;  // copy of denominator
  reg [5:0] acc;          // accumulator
  reg [2:0] ctr;          // iteration counter   
   
  initial begin
    busy <= 0;
    done <= 0;
    valid <= 0;
    dbz <= 0;
    quo <= 0;
    den_latched <= 0; 
    ctr <= 0;
  end

  assign rem = acc[5:1];

  always @(posedge clk) begin
    if (rst) begin
      busy <= 0;
      done <= 0;
      valid <= 0;
      dbz <= 0;
      quo <= 0;   
      den_latched <= 0; 
      ctr <= 0;
    end else if (go) begin
      valid <= 0;
      ctr <= 0;
      if (den == 5'b00000) begin
        busy <= 0;
        done <= 1;
        dbz <= 1;
      end else begin
        done <= 0;
        busy <= 1;
        dbz <= 0;
        den_latched <= den;
        {acc, quo} <= {5'b0, num, 1'b0};
      end
    end else begin
      if (ctr == 4) begin
	ctr <= 0;
        busy <= 0;
        done <= 1;
        valid <= 1;
      end else begin
	done <= 0;
        ctr <= ctr + 1;
      end
      if (acc >= den_latched) 
        {acc, quo} <= {acc - den_latched, quo, 1'b1};
      else
	{acc, quo} <= {acc, quo, 1'b0};
    end  
  end
   

`ifdef FORMAL
`ifdef VERIFIC
  

// 1. If go goes high and the denominator is nonzero, then in the next clock cycle, busy will be high and valid will be low.
assert property (@(posedge clk) disable iff (rst)
  go && den |=> busy && !valid);

// 2. If go goes high and the denominator is nonzero, then for the next five clock cycles, busy will be high and valid will be low.
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*0:4] |=> busy && !valid);

// 3. If go goes high and the denominator is nonzero, and go stays low for the next five clock cycles, then busy will be low and valid will be high.
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*5] |=> valid && !busy);

// 4. If go goes high and the denominator is nonzero, and go stays low for the next five clock cycles, the equation num == quo * den + rem will hold.
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*5] |=> $past(num,6) == quo * $past(den,6) + rem);

// 5. If go goes high and the denominator is nonzero, then den_latched will latch the value of den.
assert property (@(posedge clk) disable iff (rst)
  go && den |=> den_latched == $past(den));

// 6. If go goes high and the denominator is zero, then done and dbz will both go high.
assert property (@(posedge clk) disable iff (rst)
  go && !den |=> done && dbz);
   
// 7. The done signal doesn't stay high for more than one clock cycle (except when dbz is set).
assert property (@(posedge clk) disable iff (rst)
  done ##1 !dbz |-> !done);

// 8. The produced remainder will always be smaller than the denominator.
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*5] |=> rem < $past(den,6));

// 9. The produced values of quo and rem are always related by rem < 31 && rem < 32 / (quo + 1).
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*5] |=> rem < 31 && rem < 32 / (quo + 1));

// 10. All values of quo and rem that are related by rem < 31 && rem < 32 / (quo + 1) can be produced.
for (genvar q = 0; q < 32; q++)
   for (genvar r = 0; r < 32; r++)
      if (r < 32 / (q + 1) && r < 31)
        cover property (@(posedge clk) disable iff (rst)
          go && den ##1 (!go)[*5] |=> quo == q && rem == r);

wire [2:0] ctr5;        // a version of ctr that maxes out at 5 rather than 4
assign ctr5 = ctr + (5 * done);
   
wire [10:0] acc_quo;    // concatenation of acc and quo
assign acc_quo = {acc, quo};
   
wire [4:0] shifted_acc; // the middle portion of {acc,quo}
assign shifted_acc = acc_quo >> (ctr5 + 1);
   
wire [4:0] lower_quo;   // the lower bits of quo
assign lower_quo = quo & ((1 << ctr5) - 1'b1); 

reg [4:0] num_latched;  // original value of num
always @(posedge clk) if (go) num_latched <= num; 
   
// 11. A "loop invariant" that relates the intermediate values of acc and quo
assert property (@(posedge clk) disable iff (rst)
  go && den ##1 (!go)[*0:5]
  |=>
  num_latched == shifted_acc + ((lower_quo * den_latched) << (3'd5 - ctr5)));  
   
`endif
`endif
       
   
endmodule
