/**********************************************************************************
	  Module name: tb_counter                                                   
      Description: testbench
      Date: April 2022                                                      
      Auther: Sarah Mohamed Ahmed  
**********************************************************************************/
module tb_counter(ctrl, INIT, loadValue, clk, rst_l, LOSER, WINNER, WHO, GAMEOVER);
  /********************************************************************************
  	PARAMETERS
  ********************************************************************************/
  parameter cycle = 2;
  parameter COUNTER_SIZE = 4;
  /********************************************************************************
  	INPUT & OUTPUT PORTS
  ********************************************************************************/
  output ctrl, INIT, clk, loadValue, rst_l;
  input LOSER, WINNER, WHO, GAMEOVER;
  /********************************************************************************
  	REGISTERS & WIRES
  ********************************************************************************/
  reg clk;
  reg rst_l;
  reg [1:0] ctrl;
  reg [COUNTER_SIZE - 1:0] loadValue;
  reg INIT;
  
  wire [1:0] WHO;
  wire LOSER, WINNER, GAMEOVER;
  
  //Instantiate from counter module
  counter c1(.ctrl(ctrl), 
             .INIT(INIT), 
             .loadValue(loadValue), 
             .clk(clk), 
             .rst_l(rst_l), 
             .LOSER(LOSER), 
             .WINNER(WINNER), 
             .WHO(WHO), 
             .GAMEOVER(GAMEOVER));
  
  /********************************************************************************
  	CLOCK GENERATIONS
  ********************************************************************************/
  initial begin 
    clk = 0;
    forever #(cycle/2) clk = ~clk;
  end
  /********************************************************************************
  	INITIAL BLOCK
  ********************************************************************************/
  initial begin
    loadValue = 4'b0000;
    ctrl = 2'b00;
    rst_l = 1;
    INIT = 0;
    clk = 1;
    for (int ctrl_c = 0; ctrl_c <= 3; ctrl_c = ctrl_c + 1) begin 
      for (int loadValue_c = 0; loadValue_c < 3; loadValue_c = loadValue_c + 1) begin   
        #1
        rst_l <= 1;
        #1
        INIT <= 1;
        ctrl <= ctrl_c;
        if(loadValue_c == 2) loadValue <= {COUNTER_SIZE{1'b1}};
        else loadValue <= loadValue_c;
        #2
        INIT <= 0;

        #500
        rst_l <= 0;
      end
    end
  end
  
  /********************************************************************************
  	DUMP VARIABLES
  ********************************************************************************/
  initial begin
    $dumpfile("wave.vcd");
    $dumpvars;
    #6000 $finish;
  end
endmodule