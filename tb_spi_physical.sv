`timescale 1us/1ns
`include "agent_spi_slave.sv"

module tb_spi_physical;

    const integer t_clk    = 10;    // Clock period 100MHz

    logic        clk;
    logic        nrst;

    logic        ena;
    logic        msb_first;
    logic        delay_byte;
    logic [7:0]  n_delay_byte;
    logic        cpol;
    logic        cpha;
    logic [23:0] clk_div;
    logic        new_byte;
    logic        system_idle;
    logic [7:0]  data_in;
    logic [7:0]  data_out;

    spi_if spi_if();

    spi_slave spi_slave_inst;

    spi_cfg_t spi_cfg;

    spi_physical spi_physical_inst (
        .clk(clk),
        .nrst(nrst),

        // Control signals
        .ena(ena),
        .msb_first(msb_first),
        .delay_byte(delay_byte),
        .n_delay_byte(n_delay_byte),
        .cpol(cpol),
        .cpha(cpha),
        .clk_div(clk_div),
        .new_byte(new_byte),
        .system_idle(system_idle),
        .data_in(data_in),
        .data_out(data_out),

        // SPI signals
        .spi_clk(spi_if.sclk),
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
    endtask

    task automatic master_send_byte(logic [7:0] data);
        data_in = data;
        ena = 1;
        @(posedge clk);
        @(posedge clk iff new_byte);
        ena = 0;
    endtask

    task automatic master_recv_byte(ref logic [7:0] data);
        ena = 1;
        @(posedge clk);
        @(posedge clk iff new_byte);
        data = data_out;
        ena = 0;
    endtask

    // Clock generation
    initial begin
        clk = 0;
        forever #(t_clk/2) clk = ~clk;
    end

    // Reset generation
    initial begin
        nrst = 0;
        ena = 0;
        msb_first = 0;
        delay_byte = 0;
        n_delay_byte = 0;
        cpol = 0;
        cpha = 0;
        clk_div = 0;
        data_in = 0;
        spi_slave_inst = new(spi_if);
        spi_slave_inst.reset_if();
        data_in = 0;
        #111;
        nrst = 1;
    end

    
    initial begin
        // Wait for reset deassertion
        @(posedge nrst);
        @(posedge clk);

        // Test configuration
        spi_cfg.msb_first = 1;
        spi_cfg.delay_byte = 1;
        spi_cfg.n_delay_byte = 5;
        spi_cfg.cpol = 0;
        spi_cfg.cpha = 0;
        spi_cfg.clk_div = 10; // 10MHz SPI clock

        configure_spi(spi_cfg);

        // Test master sending a byte
        fork
            master_send_byte(8'b11100101);
            spi_slave_inst.read();
        join

        @(posedge clk iff system_idle);
        #100 @(posedge clk);

        // Test master receiving a byte
        fork
            master_recv_byte(data_out);
            spi_slave_inst.write();
        join

        @(posedge clk iff system_idle);
        #100 @(posedge clk);
        $finish;
    end

endmodule