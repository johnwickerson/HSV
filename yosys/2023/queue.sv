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

   // TODO: assertions go here
   
`endif
   
endmodule
