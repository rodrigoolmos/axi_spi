module axi_s_to_fifos_spi #(
    parameter integer FIFO_DEPTH = 32,
    parameter integer C_DATA_WIDTH = 32
)(
    input  logic                     clk,
    input  logic                     nrst,

    // AXI4-Lite SLAVE
    input  logic [31:0]  awaddr,
    input  logic [3:0]               awprot,
    input  logic                     awvalid,
    output logic                     awready,

    input  logic [C_DATA_WIDTH-1:0]  wdata,
    input  logic [C_DATA_WIDTH/8-1:0] wstrb,
    input  logic                     wvalid,
    output logic                     wready,

    output logic [1:0]               bresp,
    output logic                     bvalid,
    input  logic                     bready,

    input  logic [31:0]  araddr,
    input  logic [3:0]               arprot,
    input  logic                     arvalid,
    output logic                     arready,

    output logic [C_DATA_WIDTH-1:0]  rdata,
    output logic [1:0]               rresp,
    output logic                     rvalid,
    input  logic                     rready,


    // FIFO write interface
    input logic [C_DATA_WIDTH-1:0]  fifo_wdata,
    input logic                     fifo_wena,

    // FIFO read interface
    output logic [C_DATA_WIDTH-1:0] fifo_rdata,
    input logic                     fifo_rena,

    // SPI control signals
    input logic                     spi_busy,
    output logic                    spi_ena,

    // SPI configuration outputs
    output logic        msb_first,      // MSB first or LSB first
    output logic        delay_byte,     // Delay between bytes
    output logic [7:0]  n_delay_byte,   // Number of spi clock cycles to delay between bytes
    output logic        cpol,           // Clock polarity
    output logic        cpha,           // Clock phase
    output logic [23:0] clk_div         // Clock divider for SPI clock generation clk_div >= 5

);

    localparam ADDR_STATUS    = 0;
    localparam ADDR_WRITE     = 1;
    localparam ADDR_READ      = 2;
    localparam ADDR_N_BYTE_R  = 3;
    localparam ADDR_N_BYTE_W  = 4;
    localparam ADDR_DELAYS    = 5;
    localparam ADDR_CLK_DIV   = 6;
    localparam ADDR_CFG       = 7;


    localparam BYTES        = C_DATA_WIDTH/8;
    localparam ADDR_LSB     = $clog2(BYTES); 

    logic [C_DATA_WIDTH-1:0]    reg_write   [0:FIFO_DEPTH-1];
    logic [C_DATA_WIDTH-1:0]    reg_read    [0:FIFO_DEPTH-1];
    logic [31:0]                araddr_reg;
    logic [31:0]                awaddr_reg;
    logic [C_DATA_WIDTH-1:0]    wdata_reg;

    logic [$clog2(FIFO_DEPTH)-1:0]     n_bytes_to_read;
    logic [$clog2(FIFO_DEPTH)-1:0]     n_bytes_to_read_reg;
    logic                              n_bytes_to_read_update;
    logic [$clog2(FIFO_DEPTH)-1:0]     n_bytes_to_write;
    logic [$clog2(FIFO_DEPTH)-1:0]     n_bytes_to_write_reg;
    logic                              n_bytes_to_write_update;

    logic full2;
    logic almost_full2;
    logic empty2;
    logic almost_empty2;

    logic full1;
    logic almost_full1;
    logic empty1;
    logic almost_empty1;

    logic wrote_axi;
    logic push_fifo1;
    logic pop_fifo1;
    logic push_fifo2;
    logic pop_fifo2;
    localparam int INDEX_W = $clog2(FIFO_DEPTH);
    logic [INDEX_W-1:0] write_index_axi, read_index_axi;
    logic [INDEX_W-1:0] write_index_fifo, read_index_fifo;
    logic [INDEX_W:0]   size_fifo1, size_fifo2;

    typedef enum logic {
        IDLE_READ,
        READ_DATA
    } state_read;
    state_read state_r;

    // AXI READ CHANNEL AND FIFO WRITE CHANNEL
    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            arready             <= 0;
            araddr_reg          <= 0;
            rdata               <= 0;
            rresp               <= 0;
            rvalid              <= 0;
            state_r             <= IDLE_READ;
            read_index_axi      <= 0;
        end else begin
            case (state_r)
                IDLE_READ: begin
                    arready     <= 1;
                    if (arvalid && arready) begin
                        araddr_reg  <= araddr;
                        state_r     <= READ_DATA;
                        arready <= 0;
                    end
                end

                READ_DATA: begin
                    rvalid  <= 1;
                    rresp   <= 0;

                    if (araddr_reg[31:ADDR_LSB] == ADDR_STATUS) begin
                        rdata   <= {27'b0,
                                    spi_busy, 
                                    full2,
                                    almost_full2,
                                    empty1,
                                    almost_empty1};
                                    
                    end else if (araddr_reg[31:ADDR_LSB] == ADDR_READ) begin
                        rdata   <= reg_read[read_index_axi];
                    end
                    if (rready && rvalid) begin
                        if (araddr_reg[31:ADDR_LSB] == ADDR_READ && !empty1) begin
                            read_index_axi <= read_index_axi + 1;
                            if (read_index_axi == FIFO_DEPTH - 1) begin
                                read_index_axi <= 0;
                            end
                        end
                        rvalid  <= 0;
                        state_r <= IDLE_READ;
                    end
                end

                default: begin
                    state_r <= IDLE_READ;
                end
            endcase

        end
    end

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            reg_read            <= '{default: '0};
            write_index_fifo    <= 0;
        end else begin
            if (fifo_wena && !full1) begin
                reg_read[write_index_fifo] <= fifo_wdata;
                write_index_fifo <= write_index_fifo + 1;
                if (write_index_fifo == FIFO_DEPTH - 1) begin
                    write_index_fifo <= 0;
                end
            end
        end
    end

    always_comb begin
        push_fifo1 = (fifo_wena && !full1);
        pop_fifo1 = (araddr_reg[31:ADDR_LSB] == ADDR_READ && !empty1) && 
                (state_r == READ_DATA) && (rready && rvalid);
    end

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            size_fifo1 <= FIFO_DEPTH;
        end else begin
            size_fifo1 <= size_fifo1 + pop_fifo1 - push_fifo1;
        end
    end

    typedef enum logic [1:0] {
        IDLE_WRITE,
        HAVE_AW,
        HAVE_W,
        RESP
    } state_write;
    state_write state_w;


    // AXI WRITE CHANNEL AND FIFO READ CHANNEL
    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            awready         <= 0;
            wready          <= 0;
            bvalid          <= 0;
            bresp           <= 0;
            awaddr_reg      <= 0;
            wdata_reg       <= 0;
            wrote_axi       <= 0;
            write_index_axi <= 0;
            n_bytes_to_write_reg <= 0;
            n_bytes_to_read_reg <= 0;
            n_bytes_to_write_update <= 0;
            n_bytes_to_read_update <= 0;
            delay_byte <= 0;
            n_delay_byte <= 0;
            clk_div <= 0;
            msb_first <= 0;
            cpol <= 0;
            cpha <= 0;
            state_w         <= IDLE_WRITE;
            reg_write       <= '{default: '0};
        end else begin
            case (state_w)
                IDLE_WRITE: begin
                    awready <= 1;
                    wready  <= 1;
                    wrote_axi   <= 0;
                    if ((wvalid && wready) && (awvalid && awready)) begin
                        wdata_reg   <= wdata;
                        awaddr_reg  <= awaddr;
                        wready      <= 0;
                        awready     <= 0;
                        state_w     <= RESP;
                    end else if (awvalid && awready) begin
                        awaddr_reg  <= awaddr;
                        awready     <= 0;
                        state_w     <= HAVE_AW;
                    end else if (wvalid && wready) begin
                        wdata_reg   <= wdata;
                        wready      <= 0;
                        state_w     <= HAVE_W;
                    end

                end

                HAVE_AW: begin
                    wready  <= 1;
                    if (wvalid && wready) begin
                        wdata_reg   <= wdata;
                        wready      <= 0;
                        state_w     <= RESP;
                    end
                end

                HAVE_W: begin
                    awready <= 1;
                    if (awvalid && awready) begin
                        awaddr_reg  <= awaddr;
                        awready     <= 0;
                        state_w     <= RESP;
                    end
                end

                RESP: begin
                    if (awaddr_reg[31:ADDR_LSB] == ADDR_WRITE && !wrote_axi && !full2) begin
                        reg_write[write_index_axi] <= wdata_reg;
                        write_index_axi <= write_index_axi + 1;
                        if (write_index_axi == FIFO_DEPTH - 1) begin
                            write_index_axi <= 0;
                        end
                        wrote_axi <= 1;
                    end else if (awaddr_reg[31:ADDR_LSB] == ADDR_N_BYTE_R) begin
                        n_bytes_to_read_reg <= wdata_reg;
                        n_bytes_to_read_update <= 1;
                    end else if (awaddr_reg[31:ADDR_LSB] == ADDR_N_BYTE_W) begin
                        n_bytes_to_write_reg <= wdata_reg;
                        n_bytes_to_write_update <= 1;
                    end else if (awaddr_reg[31:ADDR_LSB] == ADDR_DELAYS) begin
                        delay_byte <= wdata_reg[8];
                        n_delay_byte <= wdata_reg[7:0];
                    end else if (awaddr_reg[31:ADDR_LSB] == ADDR_CLK_DIV) begin
                        clk_div <= wdata_reg[23:0];
                    end else if (awaddr_reg[31:ADDR_LSB] == ADDR_CFG) begin
                        msb_first <= wdata_reg[0];
                        cpol <= wdata_reg[1];
                        cpha <= wdata_reg[2];
                    end
                    bvalid  <= 1;
                    bresp   <= 0;
                    if (bready && bvalid) begin
                        bvalid  <= 0;
                        n_bytes_to_write_update <= 0;
                        n_bytes_to_read_update <= 0;
                        state_w <= IDLE_WRITE;
                    end
                end

                default: begin
                    state_w <= IDLE_WRITE;
                end
            endcase

        end
    end

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            read_index_fifo <= 0;
        end else begin
            if (fifo_rena && !empty2) begin
                read_index_fifo <= read_index_fifo + 1;
                if (read_index_fifo == FIFO_DEPTH - 1) begin
                    read_index_fifo <= 0;
                end
            end
        end
    end

    always_comb begin
        pop_fifo2 = (fifo_rena && !empty2);
        push_fifo2 = (awaddr_reg[31:ADDR_LSB] == ADDR_WRITE && !wrote_axi && !full2) && (state_w == RESP);
    end

    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            size_fifo2 <= FIFO_DEPTH;
        end else begin
            size_fifo2 <= size_fifo2 + pop_fifo2 - push_fifo2;
        end
    end

    always_comb fifo_rdata = reg_write[read_index_fifo];

    // Status signals
    always_comb begin
        // FIFO 2 - READ CHANNEL FIFO
        empty2        = size_fifo2 == FIFO_DEPTH;
        almost_empty2 = size_fifo2 == (FIFO_DEPTH - 1);
        full2         = size_fifo2 == 0;
        almost_full2  = size_fifo2 == 1;

        // FIFO 1 - WRITE CHANNEL FIFO
        empty1         = size_fifo1 == FIFO_DEPTH;
        almost_empty1  = size_fifo1 == (FIFO_DEPTH - 1);
        full1          = size_fifo1 == 0;
        almost_full1   = size_fifo1 == 1;
    end

    typedef enum logic [1:0] { IDLE_SPI, SENDING_SPI, RECEIVING_SPI } state_spi_t;
    state_spi_t state_spi;


    always_ff @(posedge clk or negedge nrst) begin
        if (!nrst) begin
            state_spi <= IDLE_SPI;
            spi_ena <= 0;
            n_bytes_to_read <= 0;
            n_bytes_to_write <= 0;
        end else begin
            case (state_spi)
                IDLE_SPI: begin
                    spi_ena <= 0;
                    if (n_bytes_to_write_update) begin
                        n_bytes_to_write <= n_bytes_to_write_reg;
                    end
                    if (n_bytes_to_read_update) begin
                        n_bytes_to_read <= n_bytes_to_read_reg;
                    end
                    if (!spi_busy) begin
                        if (n_bytes_to_write) begin
                            spi_ena <= 1;
                            state_spi <= SENDING_SPI;
                        end else if (n_bytes_to_read) begin
                            spi_ena <= 1;
                            state_spi <= RECEIVING_SPI;
                        end
                    end
                end

                SENDING_SPI: begin
                    if (fifo_rena) begin
                        if (n_bytes_to_write) begin
                            n_bytes_to_write <= n_bytes_to_write - 1;
                        end
                    end
                    if (n_bytes_to_write == 0 || empty2) begin
                        if (n_bytes_to_read) begin
                            state_spi <= RECEIVING_SPI;
                        end else begin
                            state_spi <= IDLE_SPI;
                            spi_ena <= 0;
                        end
                    end
                end

                RECEIVING_SPI: begin
                    if (fifo_wena) begin
                        if (n_bytes_to_read) begin
                            n_bytes_to_read <= n_bytes_to_read - 1;
                        end
                    end
                    if (n_bytes_to_read == 0 || full1) begin
                        state_spi <= IDLE_SPI;
                        spi_ena <= 0;
                    end
                end

                default: begin
                    state_spi <= IDLE_SPI;
                end
            endcase
        end
    end

endmodule