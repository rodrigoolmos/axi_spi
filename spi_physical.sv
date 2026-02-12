module spi_physical(
    input  logic        clk,
    input  logic        nrst,

    // Control signals
    input  logic        ena,
    input  logic        msb_first,      // MSB first or LSB first
    input  logic        delay_byte,     // Delay between bytes
    input  logic [7:0]  n_delay_byte,   // Number of spi clock cycles to delay between bytes
    input  logic        cpol,           // Clock polarity
    input  logic        cpha,           // Clock phase
    input  logic [23:0] clk_div,        // Clock divider for SPI clock generation clk_div >= 5
    output logic        new_byte,       // Indicates a new byte is ready to be transmitted or received
    output logic        system_idle,    // Indicates the system is idle
    input  logic [7:0]  data_in,        // Data to be transmitted
    output logic [7:0]  data_out,       // Received data

    // SPI signals
    output logic        spi_clk,
    output logic        spi_mosi,
    input  logic        spi_miso,
    output logic        spi_cs_n
);
    
    logic [23:0] clk_div_cnt;
    logic [7:0]  data_in_ff;
    logic [7:0]  bits_send_cnt;
    logic read_miso;
    logic set_mosi;
    logic end_clk_cnt;
    logic rst_cnts;
    logic end_operating;

    typedef enum logic [1:0] { IDLE, OPERATING, WAITING, LOAD_BYTE } state_spi_t;
    state_spi_t state_spi;

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            state_spi <= IDLE;
            data_in_ff <= 0;
            rst_cnts <= 0;
            data_out <= 0;
        end else begin
            case (state_spi)
                IDLE: begin
                    rst_cnts <= 1;
                    if (ena) begin
                        state_spi <= delay_byte ? WAITING : LOAD_BYTE;
                    end
                end
                LOAD_BYTE: begin
                    rst_cnts <= 0;
                    if (ena) begin
                        state_spi <= OPERATING;
                        data_in_ff <= data_in;
                    end else begin
                        state_spi <= IDLE;
                    end
                end
                OPERATING: begin
                    if (set_mosi) data_in_ff <= msb_first ? 
                        {data_in_ff[6:0], 1'b0} : {1'b0, data_in_ff[7:1]};
                    if (read_miso) data_out <= msb_first ? 
                        {data_out[6:0], spi_miso} : {spi_miso, data_out[7:1]};

                    if (end_operating) begin
                        rst_cnts <= 1;
                        state_spi <= delay_byte ? WAITING : LOAD_BYTE;
                    end
                end
                WAITING: begin
                    rst_cnts <= 0;
                    if (bits_send_cnt == n_delay_byte) begin
                        rst_cnts <= 1;
                        state_spi <= LOAD_BYTE;
                    end
                end
            endcase
        end
    end


    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            clk_div_cnt <= 0;
        end else if (rst_cnts) begin
            clk_div_cnt <= 0;
        end else begin
            if (end_clk_cnt) begin
                clk_div_cnt <= 0;
            end else begin
                clk_div_cnt <= clk_div_cnt + 1;
            end
        end
    end

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            bits_send_cnt <= 0;
        end else if (rst_cnts) begin
            bits_send_cnt <= 0;
        end else begin
            if (end_clk_cnt) begin
                bits_send_cnt <= bits_send_cnt + 1;
            end
        end
    end

    assign read_miso = (cpha ? end_clk_cnt : clk_div_cnt == (clk_div >> 1)) 
                            && state_spi == OPERATING;
    assign set_mosi = (cpha ? clk_div_cnt == (clk_div >> 1) : clk_div_cnt == 0) 
                            && bits_send_cnt != 0 && state_spi == OPERATING;
    assign end_clk_cnt = (clk_div_cnt == clk_div);
    assign spi_clk = cpol ^ ((clk_div_cnt > (clk_div >> 1)) && (state_spi == OPERATING));
    assign end_operating = (bits_send_cnt == 8) && clk_div_cnt == (clk_div >> 1)-1;
    assign spi_mosi = (state_spi == OPERATING) ? (msb_first ? data_in_ff[7] : data_in_ff[0]) : 1'b0;
    assign spi_cs_n = (state_spi == IDLE) ? 1 : 0;
    assign system_idle = (state_spi == IDLE);
    assign new_byte = end_operating;

endmodule