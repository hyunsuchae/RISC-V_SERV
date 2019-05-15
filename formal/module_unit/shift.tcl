#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

clear -all
#Reading the files (.v and .sv) 
analyze -v2k {../rtl/ser_shift.v}

analyze -sv v_ser_shift.sv

#Elaborating the design, specify the top module
#elaborate -top ser_add
elaborate -top ser_shift

#You may  need to add commands below

#Set the clock
clock i_clk

#Set Reset
reset i_rst

#Prove all
prove -bg -all
