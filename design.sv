/***********************************************************************************
      Module name: counter                                                   
      Description: multi-mode counter. It can count up, down, by ones and by twos. 
                   There is a two-bit control bus input indicating which one of 
                   the four modes is active.
      Date: April 2022                                                      
      Auther: Sarah Mohamed Ahmed  
***********************************************************************************/
module counter(ctrl, INIT, loadValue, clk,rst_l, LOSER, WINNER, WHO, GAMEOVER);
  /*********************************************************************************
  	PARAMETERS
  *********************************************************************************/
  parameter COUNTER_SIZE = 4;
  parameter cycle = 2;         // clock cycle = 2 msec.
  parameter whoValue = 2'b00;  //start value
  parameter upOne = 2'b00;     //00 count up by 1
  parameter upTwo = 2'b01;     //01 count up by 2
  parameter downOne = 2'b10;   //10 count down by 1
  parameter downTwo = 2'b11;   //11 count down by 2
  
  /********************************************************************************
  	INPUT & OUTPUT PORTS
  ********************************************************************************/
  input ctrl, INIT, clk, loadValue, rst_l;
  output LOSER, WINNER, WHO, GAMEOVER;
  
  /********************************************************************************
  	REGISTERS & WIRES
  ********************************************************************************/
  reg LOSER;
  reg WINNER;
  reg GAMEOVER;
  reg [1:0] WHO;
  reg [1:0] ctrl;
  reg [COUNTER_SIZE - 1:0] counter;
  reg [COUNTER_SIZE - 1:0] loser_count;
  reg [COUNTER_SIZE - 1:0] win_count;
  wire [COUNTER_SIZE - 1:0] loadValue;
  
  /********************************************************************************
  	INITIALIZATION
  ********************************************************************************/
  initial begin 
    counter = loadValue;
    WHO = whoValue;
    loser_count = 0;
    win_count = 0;
    LOSER = 0;
    WINNER = 0;
    GAMEOVER = 0;
  end
  
  /********************************************************************************
  	ALWAYS BLOCK
  ********************************************************************************/
  always @(posedge clk) begin
    /*************************
      SYNCHRONOUS RESET
    *************************/
    if (~rst_l || GAMEOVER) begin
      counter <= 4'b0000;            
      LOSER <= 0;                   
      WINNER <= 0;
      WHO <= 2'b00;
      loser_count <= 0;
      win_count <= 0;
      GAMEOVER <= 0;
    end
    /*************************
      INITIALIZATION
    *************************/
    else if (INIT) begin
      counter <= loadValue;
      loser_count <= 0;
      win_count <= 0;
      WHO <= 2'b00;
      WINNER <= 0;
      LOSER <= 0;
      GAMEOVER <= 0;

    end
    else begin    
      case (ctrl)
        upOne: 	counter <= counter + 1; 
        upTwo: 	counter <= counter + 2;
        downOne:  counter <= counter - 1; 
        downTwo:  counter <= counter - 2;
      endcase
      /***************************************************************************
          set LOSER signal to 1 for 1 clock cycle then clear it and increase 
          loser counter by 1 if counter reaches 0
      ***************************************************************************/
      if(counter == 0) begin
        LOSER <= 1;
        WINNER <= 0;
        loser_count <= loser_count + 1;
      end
      /***************************************************************************
          set WINNER signal to 1 for 1 clock cycle then clear it and increase 
          winner counter by 1 if counter reaches 15
      ***************************************************************************/
      else if(counter == 15) begin
        WINNER <= 1;
        LOSER <= 0;
        win_count <= win_count + 1;
      end
      else begin
        LOSER <= 0;
        WINNER <= 0;
      end
      // raise gameover signal if loser or winner counter reaches 15
      if(loser_count == 15 || win_count == 15) begin
        GAMEOVER <= 1;
        if(loser_count == 15) WHO <= 2'b01;
        else WHO <= 2'b10;
      end
	end
  end 
endmodule
