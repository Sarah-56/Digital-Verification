interface Counter_Interface #(
  parameter COUNTER_SIZE = 4
)(
    input bit clk
    );
  
    logic [1:0] ctrl, WHO;
    logic INIT, LOSER, WINNER, GAMEOVER, rst_l;
    logic [COUNTER_SIZE - 1:0] loadValue;
    
    clocking cb @(posedge clk);
      default input #0ns output #0ns;
      output rst_l, ctrl, INIT, loadValue;
      input WHO, LOSER, WINNER, GAMEOVER;
    endclocking

    modport dut(
        output GAMEOVER, WHO, LOSER, WINNER,
        input clk, rst_l, ctrl, INIT, loadValue
        );
    
    modport tb
    (
      clocking cb,
      output rst_l
      
    );


endinterface

/***********************************************************************************
    Module name: counter                                                   
    Description: multi-mode counter. It can count up, down, by ones and by twos. 
                There is a two-bit control bus input indicating which one of 
                the four modes is active.
    Date: April 2022                                                      
    Auther: Sarah Mohamed Ahmed  
***********************************************************************************/
        
        module counter #( parameter COUNTER_SIZE = 4          // number of bits in counter
    )(
    Counter_Interface.dut sig
    );
//   (ctrl, INIT, loadValue, clk, rst_l, LOSER, WINNER, WHO, GAMEOVER);
    /*********************************************************************************
        PARAMETERS
   
   *********************************************************************************/
//     parameter COUNTER_SIZE = 4;
    parameter cycle = 2;         // clock cycle = 2 msec.
    parameter whoValue = 2'b00;  //start value
    parameter upOne = 2'b00;     //00 count up by 1
    parameter upTwo = 2'b01;     //01 count up by 2
    parameter downOne = 2'b10;   //10 count down by 1
    parameter downTwo = 2'b11;   //11 count down by 2
  

  /********************************************************************************
INPUT & OUTPUT PORTS
********************************************************************************/
// input ctrl, INIT, clk, loadValue, rst_l;
// output LOSER, WINNER, WHO, GAMEOVER;
    /********************************************************************************
        REGISTERS & WIRES
    ********************************************************************************/
  
  reg LOSER;
reg WINNER;
reg GAMEOVER;
reg [1:0] WHO;
reg [1:0] ctrl;
  reg [COUNTER_SIZE - 1:0] m_counter;
reg [COUNTER_SIZE - 1:0] loser_count;
reg [COUNTER_SIZE - 1:0] win_count;
wire [COUNTER_SIZE - 1:0] loadValue;
    /********************************************************************************
        INITIALIZATION
        
//     ********************************************************************************/
    initial begin 
        m_counter = sig.loadValue;
        sig.WHO = whoValue;
        loser_count = 0;
        win_count = 0;
        sig.LOSER = 0;
        sig.WINNER = 0;
        sig.GAMEOVER = 0;
    end
    
    /********************************************************************************
        ALWAYS BLOCK
    ********************************************************************************/
    always @(posedge sig.clk) begin
        /*************************
        SYNCHRONOUS RESET
        *************************/
        if (sig.rst_l || sig.GAMEOVER) begin
        m_counter <= 4'b0000;            
        sig.LOSER <= 0;                   
        sig.WINNER <= 0;
        sig.WHO <= 2'b00;
        loser_count <= 0;
        win_count <= 0;
        sig.GAMEOVER <= 0;
        end
        /*************************
        INITIALIZATION
        *************************/
        else if (sig.INIT) begin
        m_counter <= sig.loadValue;
        loser_count <= 0;
        win_count <= 0;
        sig.WHO <= 2'b00;
        sig.WINNER <= 0;
        sig.LOSER <= 0;
        sig.GAMEOVER <= 0;

        end
        else begin    
        case (sig.ctrl)
            upOne: 	m_counter <= m_counter + 1; 
            upTwo: 	m_counter <= m_counter + 2;
            downOne:  m_counter <= m_counter - 1; 
            downTwo:  m_counter <= m_counter - 2;
        endcase
        /***************************************************************************
            set LOSER signal to 1 for 1 clock cycle then clear it and increase 
            loser counter by 1 if counter reaches 0
        ***************************************************************************/
        if(m_counter == 0) begin
            sig.LOSER <= 1;
            sig.WINNER <= 0;
            loser_count = loser_count + 1;
        end
        /***************************************************************************
            set WINNER signal to 1 for 1 clock cycle then clear it and increase 
            winner counter by 1 if counter reaches 15
        ***************************************************************************/
        else if(m_counter == 15) begin
            sig.WINNER <= 1;
            sig.LOSER <= 0;
            win_count = win_count + 1;
        end
        else begin
            sig.LOSER <= 0;
            sig.WINNER <= 0;
        end
        // raise gameover signal if loser or winner counter reaches 15
        if(loser_count == 15 || win_count == 15) begin
            sig.GAMEOVER <= 1;
            if(loser_count == 15) sig.WHO <= 2'b01;
            else sig.WHO <= 2'b10;
        end
        end
    end 
endmodule