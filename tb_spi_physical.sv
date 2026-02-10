`timescale 1us/1ns

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

    logic        spi_clk;
    logic        spi_mosi;
    logic        spi_miso;
    logic        spi_cs_n;

    typedef struct packed {
        logic        msb_first;
        logic        delay_byte;
        logic [7:0]  n_delay_byte;
        logic        cpol;
        logic        cpha;
        logic [23:0] clk_div;
    } spi_cfg_t;
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
        .spi_clk(spi_clk),
        .spi_mosi(spi_mosi),
        .spi_miso(spi_miso),
        .spi_cs_n(spi_cs_n)
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

    task automatic slave_send_byte(logic [7:0] data);
        logic [7:0] data_reg = data;
        for (int i=0; i<8; ++i) begin
            if (cpha) begin
                spi_miso = msb_first ? data_reg[7] : data_reg[0];
                data_reg = msb_first ? {data_reg[6:0], 1'b0} : {1'b0, data_reg[7:1]};
                @(posedge spi_clk);
            end else begin
                spi_miso = msb_first ? data_reg[7] : data_reg[0];
                data_reg = msb_first ? {data_reg[6:0], 1'b0} : {1'b0, data_reg[7:1]};
                @(negedge spi_clk);
            end
        end
        spi_miso = 1'bz;
        @(posedge clk iff system_idle);
    endtask

    task automatic slave_recv_byte(ref logic [7:0] data);
        logic [7:0] data_reg;
        for (int i=0; i<8; ++i) begin
            if (cpha) begin
                @(negedge spi_clk);
                data_reg = msb_first ? {data_reg[6:0], spi_mosi} : {spi_mosi, data_reg[7:1]};
            end else begin
                @(posedge spi_clk);
                data_reg = msb_first ? {data_reg[6:0], spi_mosi} : {spi_mosi, data_reg[7:1]};
            end
        end
        data = data_reg;
        @(posedge clk iff system_idle);
    endtask
    
    task automatic send_recv_bytes(logic [7:0] data_send_master[10],
                                    ref logic [7:0] data_recv_slave[10],
                                    int n_send, 
                                    logic [7:0] data_send_slave[10],
                                    ref logic [7:0] data_recv_master[10],
                                    int n_recv);
            for (int i=0; i<n_send; ++i) begin
                fork
                    master_send_byte(data_send_master[i]);
                    slave_recv_byte(data_recv_slave[i]);
                join
            end
            for (int i=0; i<n_recv; ++i) begin
                fork
                    slave_send_byte(data_send_slave[i]);
                    master_recv_byte(data_recv_master[i]);
                join
            end        
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
        spi_miso = 1'bz;
        data_in = 0;
        #111;
        nrst = 1;
    end

    
    initial begin
        logic [7:0]  data_tmp;
        logic [7:0] data_send_master[10] = '{8'hE5, 8'hA3, 8'h7F, 8'h00, 8'hFF, 8'h12, 8'h34, 8'h56, 8'h78, 8'h9A};
        logic [7:0] data_recv_slave[10];
        logic [7:0] data_send_slave[10] = '{8'h3D, 8'hC7, 8'h81, 8'h00, 8'hFF, 8'hAB, 8'hCD, 8'hEF, 8'h01, 8'h23};
        logic [7:0] data_recv_master[10];
        int n_send = 10;
        int n_recv = 10;
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
            slave_recv_byte(data_tmp);
        join
        $display("Master sent: 0x%02X, Slave received: 0x%02X", 8'hE5, data_tmp);

        // Test slave sending a byte
        fork
            slave_send_byte(8'b00111101);
            master_recv_byte(data_tmp);
        join
        $display("Slave sent: 0x%02X, Master received: 0x%02X", 8'h3D, data_tmp);

        spi_cfg.msb_first = 0;
        configure_spi(spi_cfg);
        #100;
        @(posedge clk);

        // Test master sending a byte
        fork
            master_send_byte(8'b11100101);
            slave_recv_byte(data_tmp);
        join
        $display("Master sent: 0x%02X, Slave received: 0x%02X", 8'hE5, data_tmp);

        // Test slave sending a byte
        fork
            slave_send_byte(8'b00111101);
            master_recv_byte(data_tmp);
        join
        $display("Slave sent: 0x%02X, Master received: 0x%02X", 8'h3D, data_tmp);

        spi_cfg.cpol = 1;
        configure_spi(spi_cfg);
        #100;
        @(posedge clk);

        // Test master sending a byte
        fork
            master_send_byte(8'b11100101);
            slave_recv_byte(data_tmp);
        join
        $display("Master sent: 0x%02X, Slave received: 0x%02X", 8'hE5, data_tmp);

        // Test slave sending a byte
        fork
            slave_send_byte(8'b00111101);
            master_recv_byte(data_tmp);
        join
        $display("Slave sent: 0x%02X, Master received: 0x%02X", 8'h3D, data_tmp);


        spi_cfg.cpha = 1;
        configure_spi(spi_cfg);
        #100;
        @(posedge clk);

        // Test master sending a byte
        fork
            master_send_byte(8'b11100101);
            slave_recv_byte(data_tmp);
        join
        $display("Master sent: 0x%02X, Slave received: 0x%02X", 8'hE5, data_tmp);

        // Test slave sending a byte
        fork
            slave_send_byte(8'b00111101);
            master_recv_byte(data_tmp);
        join
        $display("Slave sent: 0x%02X, Master received: 0x%02X", 8'h3D, data_tmp);


        spi_cfg.cpha = 1;
        configure_spi(spi_cfg);
        #1000;
        @(posedge clk);
        send_recv_bytes(data_send_master, data_recv_slave, n_send, data_send_slave, data_recv_master, n_recv);
        for (int i=0; i<10; ++i) begin
            $display("Master sent: 0x%02X, Slave received: 0x%02X, Slave sent: 0x%02X, Master received: 0x%02X", 
                    data_send_master[i], data_recv_slave[i], data_send_slave[i], data_recv_master[i]);
        end

        #100;
        $finish;
    end

endmodule