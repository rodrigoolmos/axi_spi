`timescale 1ns/1ps
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

    logic        active_frame;

    spi_slave spi_slave_inst;

    spi_cfg_t spi_cfg;

    assign spi_if.clk = clk;
    assign spi_if.nrst = nrst;
    assign spi_if.spi_cfg.msb_first = msb_first;
    assign spi_if.spi_cfg.delay_byte = delay_byte;
    assign spi_if.spi_cfg.n_delay_byte = n_delay_byte;
    assign spi_if.spi_cfg.cpha = cpha;
    assign spi_if.spi_cfg.cpol = cpol;
    assign spi_if.spi_cfg.clk_div = clk_div;
    assign spi_if.active_frame = active_frame;


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
            spi_slave_inst.configure_mode(cfg);
    endtask

    task automatic master_send_byte(logic [7:0] data);
        data_in = data;
        ena = 1;
        @(posedge clk iff new_byte);
        ena = 0;
    endtask

    task automatic master_send(logic [7:0] data[]);
        foreach (data[i]) begin
            master_send_byte(data[i]);
        end
    endtask

    task automatic master_recv_byte(ref logic [7:0] data);
        ena = 1;
        @(posedge clk iff new_byte);
        data = data_out;
        ena = 0;
    endtask

    task automatic master_recv(ref logic [7:0] data[]);
        foreach (data[i]) begin
            master_recv_byte(data[i]);
        end
    endtask

    task automatic test_write_read(int ndata);
        logic [7:0] data_o[];
        logic [7:0] data_i[];

        data_o = new[ndata]; foreach (data_o[i]) data_o[i] = $urandom_range(0, 255);
        data_i = new[ndata];

        // Test master sending
        fork
            begin
                active_frame = 1;
                fork
                    master_send(data_o);
                    spi_slave_inst.read();
                join
                active_frame = 0;
            end
            begin
                spi_slave_inst.frame_assertions(data_o.size());
            end
        join

        @(posedge clk iff system_idle);
        #100 @(posedge clk);

        // Test master receiving
        fork
            begin
                active_frame = 1;
                fork
                    spi_slave_inst.write();
                    master_recv(data_i);
                join
                active_frame = 0;
            end
            begin
                spi_slave_inst.frame_assertions(data_i.size());
            end
        join

        // check integrity of received
        foreach (data_i[i]) begin 
            assert (data_i[i] == data_o[i]) 
                $display("Data match at index %0d: expected 0b%08b, got 0b%08b", i, data_o[i], data_i[i]);
            else begin
                $error("Data mismatch at index %0d: expected 0b%08b, got 0b%08b", i, data_o[i], data_i[i]);
                $stop;
            end 
        end

    endtask

    task automatic test_write_read_data(input logic [7:0] data_o[]);
        logic [7:0] data_i[];

        data_i = new[data_o.size()];

        // Test master sending
        fork
            begin
                active_frame = 1;
                fork
                    master_send(data_o);
                    spi_slave_inst.read();
                join
                active_frame = 0;
            end
            begin
                spi_slave_inst.frame_assertions(data_o.size());
            end
        join

        @(posedge clk iff system_idle);
        #100 @(posedge clk);

        // Test master receiving
        fork
            begin
                active_frame = 1;
                fork
                    spi_slave_inst.write();
                    master_recv(data_i);
                join
                active_frame = 0;
            end
            begin
                spi_slave_inst.frame_assertions(data_i.size());
            end
        join

        // check integrity of received
        foreach (data_i[i]) begin
            assert (data_i[i] == data_o[i])
                $display("Data match at index %0d: expected 0b%08b, got 0b%08b", i, data_o[i], data_i[i]);
            else begin
                $error("Data mismatch at index %0d: expected 0b%08b, got 0b%08b", i, data_o[i], data_i[i]);
                $stop;
            end
        end
    endtask

    // Simple timing checker: new_byte must be a single-cycle pulse and not occur while idle.
    property new_byte_one_cycle;
        @(posedge clk) disable iff (!nrst)
            new_byte |=> !new_byte;
    endproperty
    assert property (new_byte_one_cycle)
        else $error("new_byte is wider than 1 clk");

    property new_byte_when_active;
        @(posedge clk) disable iff (!nrst)
            new_byte |-> !system_idle;
    endproperty
    assert property (new_byte_when_active)
        else $error("new_byte asserted while system_idle");

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
        active_frame = 0;
        cpol = 0;
        cpha = 0;
        clk_div = 0;
        data_in = 0;
        spi_slave_inst = new(spi_if);
        spi_slave_inst.reset_if();
        data_in = 0;
        #100 @(posedge clk);
        nrst = 1;
    end

    
    int n_tests = 100;
    initial begin
        logic [7:0] vec[];
        // Wait for reset deassertion
        @(posedge nrst);
        @(posedge clk);

        
        // Directed tests: CPOL/CPHA modes + bit order
        spi_cfg = '{msb_first: 1, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 0, clk_div: 10};
        vec = new[2]; vec[0] = 8'h80; vec[1] = 8'hA5;
        $display("Directed Test M0 MSB: 80 A5");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 0, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 0, clk_div: 10};
        vec = new[2]; vec[0] = 8'h01; vec[1] = 8'hA5;
        $display("Directed Test M0 LSB: 01 A5");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 1, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 1, clk_div: 10};
        vec = new[2]; vec[0] = 8'h80; vec[1] = 8'h3C;
        $display("Directed Test M1 MSB: 80 3C");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 0, delay_byte: 0, n_delay_byte: 0, cpol: 1, cpha: 0, clk_div: 10};
        vec = new[2]; vec[0] = 8'h01; vec[1] = 8'h3C;
        $display("Directed Test M2 LSB: 01 3C");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 1, delay_byte: 0, n_delay_byte: 0, cpol: 1, cpha: 1, clk_div: 10};
        vec = new[2]; vec[0] = 8'h80; vec[1] = 8'hA5;
        $display("Directed Test M3 MSB: 80 A5");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 0, delay_byte: 0, n_delay_byte: 0, cpol: 1, cpha: 1, clk_div: 10};
        vec = new[2]; vec[0] = 8'h01; vec[1] = 8'hA5;
        $display("Directed Test M3 LSB: 01 A5");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);


        // Edge-case tests: clk_div min/even and delay_byte behavior
        spi_cfg = '{msb_first: 1, delay_byte: 0, n_delay_byte: 0, cpol: 0, cpha: 0, clk_div: 5};
        vec = new[3]; vec[0] = 8'hFF; vec[1] = 8'h00; vec[2] = 8'h81;
        $display("Edge Test clk_div=5 M0 MSB: FF 00 81");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 0, delay_byte: 0, n_delay_byte: 0, cpol: 1, cpha: 0, clk_div: 6};
        vec = new[2]; vec[0] = 8'h3C; vec[1] = 8'hC3;
        $display("Edge Test clk_div=6 M2 LSB: 3C C3");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 1, delay_byte: 1, n_delay_byte: 0, cpol: 0, cpha: 1, clk_div: 10};
        vec = new[2]; vec[0] = 8'h5A; vec[1] = 8'hA5;
        $display("Edge Test delay_byte=1 n=0 (no delay) M1 MSB: 5A A5");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 1, delay_byte: 1, n_delay_byte: 1, cpol: 0, cpha: 1, clk_div: 10};
        vec = new[4]; vec[0] = 8'hA5; vec[1] = 8'h5A; vec[2] = 8'h01; vec[3] = 8'h80;
        $display("Edge Test delay_byte=1 n=1 M1 MSB: A5 5A 01 80");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);

        spi_cfg = '{msb_first: 0, delay_byte: 1, n_delay_byte: 10, cpol: 1, cpha: 1, clk_div: 10};
        vec = new[3]; vec[0] = 8'h0F; vec[1] = 8'hF0; vec[2] = 8'hAA;
        $display("Edge Test delay_byte=1 n=10 M3 LSB: 0F F0 AA");
        configure_spi(spi_cfg);
        #1000 @(posedge clk);
        test_write_read_data(vec);


        for (int i = 0; i < n_tests; i++) begin
            
            // Test configuration
            spi_cfg.msb_first = $urandom_range(0, 1);
            spi_cfg.delay_byte = $urandom_range(0, 1);
            spi_cfg.n_delay_byte = $urandom_range(0, 10);
            spi_cfg.cpol = $urandom_range(0, 1);
            spi_cfg.cpha = $urandom_range(0, 1);
            spi_cfg.clk_div = $urandom_range(5, 110);

            $display("Test %0d: msb_first=%b, delay_byte=%b, n_delay_byte=%0d, cpol=%b, cpha=%b, clk_div=%0d",
                        i, spi_cfg.msb_first, spi_cfg.delay_byte, spi_cfg.n_delay_byte,
                        spi_cfg.cpol, spi_cfg.cpha, spi_cfg.clk_div);
    
            configure_spi(spi_cfg);
            #1000 @(posedge clk);

            test_write_read($urandom_range(1, 20));
        end



        @(posedge clk iff system_idle);
        #100 @(posedge clk);

        $display("All tests passed!");
        $finish;
    end

endmodule
