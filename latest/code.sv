/*************
    Design
**************/
interface Counter_Interface #(
  parameter COUNTER_SIZE = 4
)(
    input bit clk
    );
  
    bit [1:0] ctrl, WHO;
    bit INIT, LOSER, WINNER, GAMEOVER, rst_l;
    bit [COUNTER_SIZE - 1:0] loadValue;

    clocking cb @(posedge clk);
      default input #0ns output #1ns;
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

 module counter #( 
    parameter COUNTER_SIZE = 4          // number of bits in counter
    )(
    Counter_Interface.dut sig
    );
    /*********************************************************************************
        PARAMETERS
    *********************************************************************************/
    parameter cycle = 2;         // clock cycle = 2 msec.
    parameter whoValue = 2'b00;  //start value
    parameter upOne = 2'b00;     //00 count up by 1
    parameter upTwo = 2'b01;     //01 count up by 2
    parameter downOne = 2'b10;   //10 count down by 1
    parameter downTwo = 2'b11;   //11 count down by 2
  
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
        ALWAYS BLOCK
    ********************************************************************************/
    always @(posedge sig.clk) begin
        if (sig.INIT) begin
            m_counter = sig.loadValue;
            sig.WHO = whoValue;
            loser_count = 0;
            win_count = 0;
            sig.LOSER = 0;
            sig.WINNER = 0;
            sig.GAMEOVER = 0;
        end
        else begin
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
    end 
endmodule


/********************************************************************************
    TB
********************************************************************************/
program tb_counter(Counter_Interface.tb sig);
    /********************************************************************************
        PARAMETERS
    ********************************************************************************/
    parameter cycle = 2;
    parameter COUNTER_SIZE = 4;
    /********************************************************************************
        INITIAL BLOCK
    ********************************************************************************/
    initial begin
        sig.cb.loadValue <= 4'b0000;
        sig.cb.ctrl <= 2'b00;
        sig.cb.rst_l <= 0;
        sig.cb.INIT <= 1;
        for (int ctrl_c = 0; ctrl_c <= 3; ctrl_c = ctrl_c + 1) begin 
            for (int loadValue_c = 0; loadValue_c < 3; loadValue_c = loadValue_c + 1) begin   
                // sig.rst_l <= 1;
                assertion_1: assert (sig.cb.WINNER == 0)
                    $display("WINNER = %d asserted correctly", sig.cb.WINNER);
                else 
                    $fatal("WINNER = %d not asserted correctly", sig.cb.WINNER);
                sig.cb.ctrl <= ctrl_c;
                if(loadValue_c == 2) sig.cb.loadValue <= {COUNTER_SIZE{1'b1}};
                else sig.cb.loadValue <= loadValue_c;
                sig.cb.INIT <= 0;
                #2
                sig.cb.rst_l <= 0;
              	#2
                sig.cb.INIT <= 1;
                #1
                sig.cb.INIT <= 0;
                #481
                sig.cb.rst_l <= 1;
            end
        end
    end
    /****************************
        Assign BLOCK
    ****************************/
    assign WHO = sig.cb.WHO;
    assign LOSER = sig.cb.LOSER;
    assign WINNER = sig.cb.WINNER;
    assign GAMEOVER = sig.cb.GAMEOVER;  
    /****************************
        Properties
    ****************************/
    property reset_signals;
      @(sig.cb) disable iff(!($fell(sig.rst_l) )) (WHO ==0 || LOSER == 0 || GAMEOVER == 0 || WINNER ==0);
    endproperty

    property winner;
      @(sig.cb)
      if($fell(sig.rst_l)) ##[150:250] GAMEOVER == 1;
    endproperty

    /****************************
        Asserions
    ****************************/
  	assert_winner: assert property(winner)$display("@ cycle [%0t] Assertion GameOver passed", $time / 2);
    assert_reset_signals: assert property (reset_signals) $display("@ cycle [%0t] Assertion Reseting signals passed", $time / 2);
endprogram

      

module top (output bit clk);
    initial clk = 1;
    initial forever #1 clk = ~clk;
    Counter_Interface iface(clk);
    tb_counter t0(iface.tb);
    counter G0(iface.dut);
    /******************************
        DUMP VARIABLES
    ******************************/
    initial begin
        $dumpfile("wave.vcd");
        $dumpvars;
    end

endmodule