unset title
set key top right
set xlabel 'Last prime < x'
set ylabel 'Time (s)'
set logscale y
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_exec_times.eps" 
set size 1.,1.

plot "sieve_cont_data_clean_realtime.txt" using 1:2 with lp title 'cont', \
"sieve_mcon_data_clean_realtime.txt" using 1:2 with lp title 'mcon', \
"sieve_dlcont_data_clean_realtime.txt" using 1:2 with lp title 'dlcont', \
"sieve_promise_data_clean_realtime.txt" using 1:2 with lp title 'promise', \
"sieve_sys_data_clean_realtime.txt" using 1:2 with lp title 'sys', \
"sieve_tramp_data_clean_realtime.txt" using 1:2 with lp title 'tramp', \
"sieve_vm_data_clean_realtime.txt" using 1:2 with lp title 'vm', \
"sieve_lwt_data_clean_realtime.txt" using 1:2 with lp title 'lwt', \
"sieve_mcon_ftt_data_clean_realtime.txt" using 1:2 with lp title 'mcon_{ftt}'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_exec_times_bw.eps" 
replot


unset title
set key top right
set xlabel 'Last prime < x'
set ylabel 'Memory (words)'
unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_mem.eps" 
set size 1.,1.

plot "sieve_cont_data_clean_mem.txt" using 1:2 with lp title 'cont', \
"sieve_mcon_data_clean_mem.txt" using 1:2 with lp title 'mcon', \
"sieve_dlcont_data_clean_mem.txt" using 1:2 with lp title 'dlcont', \
"sieve_promise_data_clean_mem.txt" using 1:2 with lp title 'promise', \
"sieve_sys_data_clean_mem.txt" using 1:2 with lp title 'sys', \
"sieve_tramp_data_clean_mem.txt" using 1:2 with lp title 'tramp', \
"sieve_vm_data_clean_mem.txt" using 1:2 with lp title 'vm', \
"sieve_lwt_data_clean_mem.txt" using 1:2 with lp title 'lwt', \
"sieve_mcon_ftt_data_clean_mem.txt" using 1:2 with lp title 'mcon_{ftt}'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_mem_bw.eps" 
replot

unset title
set key top right
set xlabel 'Last prime < x'
set ylabel 'Time (s)'
set logscale y
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_exec_times_opt.eps" 
set size 1.,1.

plot "sieve_cont_opt_data_clean_realtime.txt" using 1:2 with lp title 'cont', \
"sieve_mcon_opt_data_clean_realtime.txt" using 1:2 with lp title 'mcon', \
"sieve_dlcont_opt_data_clean_realtime.txt" using 1:2 with lp title 'dlcont', \
"sieve_promise_opt_data_clean_realtime.txt" using 1:2 with lp title 'promise', \
"sieve_sys_opt_data_clean_realtime.txt" using 1:2 with lp title 'sys', \
"sieve_tramp_opt_data_clean_realtime.txt" using 1:2 with lp title 'tramp', \
"sieve_lwt_opt_data_clean_realtime.txt" using 1:2 with lp title 'lwt', \
"sieve_mcon_ftt_opt_data_clean_realtime.txt" using 1:2 with lp title 'mcon_{ftt}'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_exec_times_opt_bw.eps" 
replot


unset title
set key top right
set xlabel 'Last prime < x'
set ylabel 'Memory (words)'
unset logscale xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_mem_opt.eps" 
set size 1.,1.

plot "sieve_cont_opt_opt_data_clean_mem.txt" using 1:2 with lp title 'cont', \
"sieve_mcon_opt_data_clean_mem.txt" using 1:2 with lp title 'mcon', \
"sieve_dlcont_opt_data_clean_mem.txt" using 1:2 with lp title 'dlcont', \
"sieve_promise_opt_data_clean_mem.txt" using 1:2 with lp title 'promise', \
"sieve_sys_opt_data_clean_mem.txt" using 1:2 with lp title 'sys', \
"sieve_tramp_opt_data_clean_mem.txt" using 1:2 with lp title 'tramp', \
"sieve_lwt_opt_data_clean_mem.txt" using 1:2 with lp title 'lwt', \
"sieve_mcon_ftt_opt_data_clean_mem.txt" using 1:2 with lp title 'mcon_{ftt}'

set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200, 20"
set output "sieve_mem_opt_bw.eps" 
replotxó
