module queue 
  #( parameter ADDR=5, // width of address bus; can be anything
     parameter DATA=42, // width of data bus; can be anything
     parameter Q_SIZE=32) // must be equal to 2 ^ ADDR 
   (
    input 		clk, // clock
    input 		rst, // reset
    input 		wen, // write-enable
    input 		ren, // read-enable
    input [DATA-1:0] 	wdata, // data in 
    output [DATA-1:0] 	rdata, // data out
    output reg [ADDR:0] count, // how many elements in queue
    output 		full, // queue is full
    output 		empty // queue is empty
    );
   
   reg [ADDR-1:0] 	waddr; // next cell to write to
   reg [ADDR-1:0] 	raddr; // next cell to read from
   reg [DATA-1:0] 	data [Q_SIZE-1:0]; // contents of queue
   
   // incrementing the write-address when write-enable is set
   initial waddr = 0;
   always @(posedge clk or posedge rst) begin
      if (rst)
	waddr <= 0;
      else if (wen || (ren && empty))
	waddr <= waddr + 1;
   end

   // incrementing the read-address when read-enable is set
   initial raddr = 0;
   always @(posedge clk or posedge rst) begin
      if (rst)
	raddr <= 0;
      else if (ren || (wen && full))
	raddr <= raddr + 1;
   end

   // updating the count
   initial count = 0;
   always @(posedge clk or posedge rst) begin
      if (rst)
        count <= 0;
      else if (wen && !ren && count < Q_SIZE)
        count <= count + 1;
      else if (ren && !wen && count > 0)
        count <= count - 1; 
   end

   // synchronously writing to the queue
   always @(posedge clk)
     if (wen) data[waddr] <= wdata;

   // asynchronously reading from the queue
   assign rdata = data[raddr];

   // setting the full/empty signals
   assign full = count == Q_SIZE;
   assign empty = (count == 0) && ~rst;

`ifdef FORMAL   
`ifdef VERIFIC

   // 1. The write-address is always less than Q_SIZE
   assert property (@(posedge clk)
		    waddr < Q_SIZE);

   // 2. The read-address is always less than Q_SIZE
   assert property (@(posedge clk)
		    raddr < Q_SIZE);

   // 3. count is always less than Q_SIZE
   // REFINES TO:
   // 3. count is always less than or equal to Q_SIZE
   assert property (@(posedge clk)
		    count <= Q_SIZE);

   // 4. Between successive clock cycles, count never changes by more than one
   // REFINES TO:
   // 4. Between successive clock cycles, count never changes by more than one, unless it is zeroed
   assert property (@(posedge clk)
		    count == 0
		    || count == $past(count)
		    || count == $past(count) + 1
		    || count == $past(count) - 1);

   // 5. The reset signal makes all the outputs go low
   assert property (@(posedge clk)
		    rst |-> 
		    !waddr && !raddr && !empty && !full && !count);

   // 6. The full signal is asserted if and only if the queue is full
   assert property (@(posedge clk)
		    full == (count == Q_SIZE));

   // 7. The empty signal is asserted if and only if the queue is empty
   // REFINES TO:
   // 7. The empty signal is asserted if and only if the queue is empty and rst is low
   assert property (@(posedge clk)
		    empty == (count == 0 && !rst));

   // 8. If the write-address and the read-address differ, then 
   //    count is calculated from their difference
   // REFINES TO:
   // 8. If the write-address and the read-address differ, then 
   //    count is calculated from their difference, modulo Q_SIZE
   assert property (@(posedge clk)
		    waddr != raddr |->
		    count == (waddr - raddr) % Q_SIZE);

   // 9. If the write-address and the read-address are the 
   //    same, then count is either Q_SIZE or 0
   assert property (@(posedge clk) 
		    waddr == raddr |-> 
		    count == Q_SIZE || count == 0);  

   // 10. rdata always holds the element of data at the read-address
   assert property (@(posedge clk) 
		    rdata == data[raddr]);

   // 11. When write-enable is set, wdata is latched into the data 
   //     array at the write-address
   assert property (@(posedge clk) 
		    wen |=> 
		    data[$past(waddr)] == $past(wdata));

   // 12. If the queue is empty and write-enable is set, then in the next 
   //     clock cycle, rdata will hold the previous value of wdata.
   // REFINES TO:
   // 12. If the queue is empty, write-enable is set, read-enable is not 
   //     set, and rst is not set, then in the next clock cycle, rdata will 
   //     hold the previous value of wdata.
   assert property (@(posedge clk) disable iff (rst) 
    		    empty && !ren && wen |=> 
		    rdata == $past(wdata));

   // 13. Setting read-enable causes the read-address to increment
   // REFINES TO:
   // 13. If rst is not set, then setting read-enable causes the
   //     read-address to increment, modulo Q_SIZE
   assert property (@(posedge clk) disable iff (rst)
		    ren |=> 
		    raddr == ($past(raddr) + 1) % Q_SIZE);

   // 14. Setting write-enable causes the write-address to increment
   // REFINES TO:
   // 13. If rst is not set, then setting write-enable causes the
   //     write-address to increment, modulo Q_SIZE
   assert property (@(posedge clk) disable iff (rst)
		    wen |=> 
		    waddr == ($past(waddr) + 1) % Q_SIZE);

   // 15. If read-enable is low, the read-address doesn't change 
   // REFINES TO:
   // 15. If read-enable is low, rst is not set, and the queue is not 
   // full, then the read-address doesn't change
   assert property (@(posedge clk) disable iff (rst)
		    !ren && !full |=> 
		    raddr == $past(raddr));

   // 16. If write-enable is low, the write-address doesn't change 
   // REFINES TO:
   // 16. If write-enable is low, rst is not set, and the queue is not 
   // empty, then the read-address doesn't change
   assert property (@(posedge clk) disable iff (rst)
		    !wen && !empty |=> 
		    waddr == $past(waddr));
   
`endif
`endif
   
endmodule
