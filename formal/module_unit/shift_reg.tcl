#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

clear -all
#Reading the files (.v and .sv) 
analyze -v2k {../rtl/shift_reg.v}

analyze -sv v_shift_reg.sv

#Elaborating the design, specify the top module
#elaborate -top ser_add
elaborate -top shift_reg

#You may  need to add commands below

#Set the clock
clock clk

#Set Reset
reset i_rst

#Prove all
prove -bg -all
