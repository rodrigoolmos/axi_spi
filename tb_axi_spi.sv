`timescale 1us/1ns
`include "axi_s_to_fifos/axi_lite_template/agent_axi_lite.sv"
`include "agent_spi_slave.sv"

module tb_axi_spi;

    const integer t_clk    = 10;    // Clock period 100MHz

    localparam ADDR_WIDTH = 32;
    localparam DATA_WIDTH = 32;

    localparam ADDR_STATUS    = 0;
    localparam ADDR_WRITE     = 1;
    localparam ADDR_READ      = 2;
    localparam ADDR_N_BYTE_R  = 3;
    localparam ADDR_N_BYTE_W  = 4;
    localparam ADDR_DELAYS    = 5;
    localparam ADDR_CLK_DIV   = 6;
    localparam ADDR_CFG       = 7;

    logic        active_frame;
    logic        msb_first;
    logic        delay_byte;
    logic [7:0]  n_delay_byte;
    logic        cpol;
    logic        cpha;
    logic [23:0] clk_div;

    spi_if spi_if();

    spi_slave spi_slave_inst;

    spi_cfg_t spi_cfg;

    assign spi_if.clk = axi_if.clk;
    assign spi_if.nrst = axi_if.nrst;
    assign spi_if.spi_cfg.msb_first = msb_first;
    assign spi_if.spi_cfg.delay_byte = delay_byte;
    assign spi_if.spi_cfg.n_delay_byte = n_delay_byte;
    assign spi_if.spi_cfg.cpha = cpha;
    assign spi_if.spi_cfg.cpol = cpol;
    assign spi_if.spi_cfg.clk_div = clk_div;
    assign spi_if.active_frame = active_frame;

    axi_if #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) axi_if();

    axi_lite_master #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) master;

    axi_spi #(
        .C_DATA_WIDTH(DATA_WIDTH),
        .FIFO_DEPTH(8)
    ) dut (
        .clk    (axi_if.clk),
        .nrst    (axi_if.nrst),

        // AXI4-Lite SLAVE
        .awaddr (axi_if.awaddr),
        .awprot (axi_if.awprot),
        .awvalid(axi_if.awvalid),
        .awready(axi_if.awready),

        .wdata  (axi_if.wdata),
        .wstrb  (axi_if.wstrb),
        .wvalid (axi_if.wvalid),
        .wready (axi_if.wready),

        .bresp  (axi_if.bresp),
        .bvalid (axi_if.bvalid),
        .bready (axi_if.bready),

        .araddr (axi_if.araddr),
        .arprot (axi_if.arprot),
        .arvalid(axi_if.arvalid),
        .arready(axi_if.arready),

        .rdata  (axi_if.rdata),
        .rresp  (axi_if.rresp),
        .rvalid (axi_if.rvalid),
        .rready (axi_if.rready),

        // SPI physical interface
        .spi_clk (spi_if.sclk),
        .spi_mosi(spi_if.mosi),
        .spi_miso(spi_if.miso),
        .spi_cs_n(spi_if.cs_n)
    );

    task automatic configure_spi(spi_cfg_t cfg);
            msb_first = cfg.msb_first;
            delay_byte = cfg.delay_byte;
            n_delay_byte = cfg.n_delay_byte;
            cpol = cfg.cpol;
            cpha = cfg.cpha;
            clk_div = cfg.clk_div;
            spi_slave_inst.configure_mode(cfg);
    endtask

    // Clock generation 
    initial begin
        axi_if.clk = 0;
        forever #(t_clk/2) axi_if.clk = ~axi_if.clk;
    end

    // Reset generation and initialization
    initial begin
        axi_if.nrst = 0;
        master = new(axi_if);
        master.reset_if();
        spi_slave_inst = new(spi_if);
        spi_slave_inst.reset_if();
        #100 @(posedge axi_if.clk);
        axi_if.nrst = 1;
        @(posedge axi_if.clk);
    end

    initial begin
        @(posedge axi_if.nrst);
        #100 @(posedge axi_if.clk);

        // Write transaction
        master.write(32'h0000_0010, ADDR_CLK_DIV*4, 4'b1111);
        master.write(32'h0000_0011, ADDR_WRITE*4, 4'b1111);
        master.write(32'h0000_0021, ADDR_WRITE*4, 4'b1111);
        master.write(32'h0000_0031, ADDR_WRITE*4, 4'b1111);
        master.write(32'h0000_0102, ADDR_DELAYS*4, 4'b1111);
        master.write(32'h0000_0003, ADDR_N_BYTE_W*4, 4'b1111);
        master.write(32'h0000_0002, ADDR_N_BYTE_R*4, 4'b1111);

        #10000 @(posedge axi_if.clk);

        $stop;

    end

endmodule