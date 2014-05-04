set title 'title'
set xlabel 'xlabel'
set ylabel 'ylabel'
set logscale y
set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14
set output "sieve_exec_times.ps" 

plot "sieve_cont_data_clean.txt" using 1:2 with lp title 'cont', \
"sieve_mcon_data_clean.txt" using 1:2 with lp title 'mcon', \
"sieve_promise_data_clean.txt" using 1:2 with lp title 'promise', \
"sieve_sys_data_clean.txt" using 1:2 with lp title 'sys', \
"sieve_tramp_data_clean.txt" using 1:2 with lp title 'tramp', \
"sieve_vm_data_clean.txt" using 1:2 with lp title 'vm', \
"sieve_lwt_data_clean.txt" using 1:2 with lp title 'lwt'


