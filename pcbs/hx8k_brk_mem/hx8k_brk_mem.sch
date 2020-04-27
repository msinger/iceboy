EESchema Schematic File Version 2
LIBS:power
LIBS:device
LIBS:transistors
LIBS:conn
LIBS:linear
LIBS:regul
LIBS:74xx
LIBS:cmos4000
LIBS:adc-dac
LIBS:memory
LIBS:xilinx
LIBS:microcontrollers
LIBS:dsp
LIBS:microchip
LIBS:analog_switches
LIBS:motorola
LIBS:texas
LIBS:intel
LIBS:audio
LIBS:interface
LIBS:digital-audio
LIBS:philips
LIBS:display
LIBS:cypress
LIBS:siliconi
LIBS:opto
LIBS:atmel
LIBS:contrib
LIBS:valves
LIBS:mem
LIBS:hx8k_brk_mem-cache
EELAYER 25 0
EELAYER END
$Descr A4 11693 8268
encoding utf-8
Sheet 1 2
Title "Iceboy HX8K-BRK Memory Module"
Date "2020-04-25"
Rev "0"
Comp "Author: Michael Singer"
Comment1 "https://sourceforge.net/projects/iceboy/"
Comment2 "http://iceboy.a-singer.de/"
Comment3 ""
Comment4 ""
$EndDescr
$Comp
L AS6C62256 U5
U 1 1 5E9F4CDD
P 7100 1700
F 0 "U5" H 6900 2700 50  0000 C CNN
F 1 "AS6C62256" H 7100 600 50  0000 C CNN
F 2 "Housings_DIP:DIP-28_W15.24mm_Socket" H 7100 1700 50  0001 C CNN
F 3 "" H 7100 1700 50  0001 C CNN
	1    7100 1700
	1    0    0    -1  
$EndComp
$Comp
L AS6C62256 U6
U 1 1 5E9F4EBF
P 7100 4000
F 0 "U6" H 6900 5000 50  0000 C CNN
F 1 "AS6C62256" H 7100 2900 50  0000 C CNN
F 2 "Housings_DIP:DIP-28_W15.24mm_Socket" H 7100 4000 50  0001 C CNN
F 3 "" H 7100 4000 50  0001 C CNN
	1    7100 4000
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U1
U 1 1 5E9F5307
P 2100 1700
F 0 "U1" H 1900 2700 50  0000 C CNN
F 1 "AS6C4008" H 2100 300 50  0000 C CNN
F 2 "Housings_DIP:DIP-32_W15.24mm_Socket" H 2100 1700 50  0001 C CNN
F 3 "" H 2100 1700 50  0001 C CNN
	1    2100 1700
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U2
U 1 1 5E9F5428
P 2100 4300
F 0 "U2" H 1900 5300 50  0000 C CNN
F 1 "AS6C4008" H 2100 2900 50  0000 C CNN
F 2 "Housings_DIP:DIP-32_W15.24mm_Socket" H 2100 4300 50  0001 C CNN
F 3 "" H 2100 4300 50  0001 C CNN
	1    2100 4300
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U3
U 1 1 5E9F546B
P 4600 1700
F 0 "U3" H 4400 2700 50  0000 C CNN
F 1 "AS6C4008" H 4600 300 50  0000 C CNN
F 2 "Housings_DIP:DIP-32_W15.24mm_Socket" H 4600 1700 50  0001 C CNN
F 3 "" H 4600 1700 50  0001 C CNN
	1    4600 1700
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U4
U 1 1 5E9F54EC
P 4600 4300
F 0 "U4" H 4400 5300 50  0000 C CNN
F 1 "AS6C4008" H 4600 2900 50  0000 C CNN
F 2 "Housings_DIP:DIP-32_W15.24mm_Socket" H 4600 4300 50  0001 C CNN
F 3 "" H 4600 4300 50  0001 C CNN
	1    4600 4300
	1    0    0    -1  
$EndComp
$Comp
L CONN_02X20 J2
U 1 1 5E9F5693
P 9750 1750
F 0 "J2" H 9750 2800 50  0000 C CNN
F 1 "CONN_02X20" V 9750 1750 50  0000 C CNN
F 2 "Pin_Headers:Pin_Header_Straight_2x20_Pitch2.54mm" H 9750 800 50  0001 C CNN
F 3 "" H 9750 800 50  0001 C CNN
	1    9750 1750
	1    0    0    -1  
$EndComp
$Comp
L CONN_02X20 J1
U 1 1 5E9F5710
P 9750 4050
F 0 "J1" H 9750 5100 50  0000 C CNN
F 1 "CONN_02X20" V 9750 4050 50  0000 C CNN
F 2 "Pin_Headers:Pin_Header_Straight_2x20_Pitch2.54mm" H 9750 3100 50  0001 C CNN
F 3 "" H 9750 3100 50  0001 C CNN
	1    9750 4050
	1    0    0    -1  
$EndComp
Wire Bus Line
	3100 700  3100 5900
Wire Bus Line
	3100 5900 10800 5900
Wire Bus Line
	5600 5900 5600 700 
Wire Bus Line
	8100 5900 8100 700 
Wire Wire Line
	2800 800  3000 800 
Wire Wire Line
	2800 900  3000 900 
Wire Wire Line
	2800 1000 3000 1000
Wire Wire Line
	2800 1100 3000 1100
Wire Wire Line
	2800 1200 3000 1200
Wire Wire Line
	2800 1300 3000 1300
Wire Wire Line
	2800 1400 3000 1400
Wire Wire Line
	2800 1500 3000 1500
Wire Wire Line
	2800 3400 3000 3400
Wire Wire Line
	2800 3500 3000 3500
Wire Wire Line
	2800 3600 3000 3600
Wire Wire Line
	2800 3700 3000 3700
Wire Wire Line
	2800 3800 3000 3800
Wire Wire Line
	2800 3900 3000 3900
Wire Wire Line
	2800 4000 3000 4000
Wire Wire Line
	2800 4100 3000 4100
Wire Wire Line
	5300 800  5500 800 
Wire Wire Line
	5300 900  5500 900 
Wire Wire Line
	5300 1000 5500 1000
Wire Wire Line
	5300 1100 5500 1100
Wire Wire Line
	5300 1200 5500 1200
Wire Wire Line
	5300 1300 5500 1300
Wire Wire Line
	5300 1400 5500 1400
Wire Wire Line
	5300 1500 5500 1500
Wire Wire Line
	5300 3400 5500 3400
Wire Wire Line
	5300 3500 5500 3500
Wire Wire Line
	5300 3600 5500 3600
Wire Wire Line
	5300 3700 5500 3700
Wire Wire Line
	5300 3800 5500 3800
Wire Wire Line
	5300 3900 5500 3900
Wire Wire Line
	5300 4000 5500 4000
Wire Wire Line
	5300 4100 5500 4100
Entry Wire Line
	3000 800  3100 900 
Entry Wire Line
	3000 900  3100 1000
Entry Wire Line
	3000 1000 3100 1100
Entry Wire Line
	3000 1100 3100 1200
Entry Wire Line
	3000 1200 3100 1300
Entry Wire Line
	3000 1300 3100 1400
Entry Wire Line
	3000 1400 3100 1500
Entry Wire Line
	3000 1500 3100 1600
Entry Wire Line
	5500 800  5600 900 
Entry Wire Line
	5500 900  5600 1000
Entry Wire Line
	5500 1000 5600 1100
Entry Wire Line
	5500 1100 5600 1200
Entry Wire Line
	5500 1200 5600 1300
Entry Wire Line
	5500 1300 5600 1400
Entry Wire Line
	5500 1400 5600 1500
Entry Wire Line
	5500 1500 5600 1600
Entry Wire Line
	3000 3400 3100 3500
Entry Wire Line
	3000 3500 3100 3600
Entry Wire Line
	3000 3600 3100 3700
Entry Wire Line
	3000 3700 3100 3800
Entry Wire Line
	3000 3800 3100 3900
Entry Wire Line
	3000 3900 3100 4000
Entry Wire Line
	3000 4000 3100 4100
Entry Wire Line
	3000 4100 3100 4200
Entry Wire Line
	5500 3400 5600 3500
Entry Wire Line
	5500 3500 5600 3600
Entry Wire Line
	5500 3600 5600 3700
Entry Wire Line
	5500 3700 5600 3800
Entry Wire Line
	5500 3800 5600 3900
Entry Wire Line
	5500 3900 5600 4000
Entry Wire Line
	5500 4000 5600 4100
Entry Wire Line
	5500 4100 5600 4200
Wire Wire Line
	7800 800  8000 800 
Wire Wire Line
	7800 900  8000 900 
Wire Wire Line
	7800 1000 8000 1000
Wire Wire Line
	7800 1100 8000 1100
Wire Wire Line
	7800 1200 8000 1200
Wire Wire Line
	7800 1300 8000 1300
Wire Wire Line
	7800 1400 8000 1400
Wire Wire Line
	7800 1500 8000 1500
Wire Wire Line
	7800 3100 8000 3100
Wire Wire Line
	7800 3200 8000 3200
Wire Wire Line
	7800 3300 8000 3300
Wire Wire Line
	7800 3400 8000 3400
Wire Wire Line
	7800 3500 8000 3500
Wire Wire Line
	7800 3600 8000 3600
Wire Wire Line
	7800 3700 8000 3700
Wire Wire Line
	7800 3800 8000 3800
Entry Wire Line
	8000 800  8100 900 
Entry Wire Line
	8000 900  8100 1000
Entry Wire Line
	8000 1000 8100 1100
Entry Wire Line
	8000 1100 8100 1200
Entry Wire Line
	8000 1200 8100 1300
Entry Wire Line
	8000 1300 8100 1400
Entry Wire Line
	8000 1400 8100 1500
Entry Wire Line
	8000 1500 8100 1600
Entry Wire Line
	8000 3100 8100 3200
Entry Wire Line
	8000 3200 8100 3300
Entry Wire Line
	8000 3300 8100 3400
Entry Wire Line
	8000 3400 8100 3500
Entry Wire Line
	8000 3500 8100 3600
Entry Wire Line
	8000 3600 8100 3700
Entry Wire Line
	8000 3700 8100 3800
Entry Wire Line
	8000 3800 8100 3900
Text Label 2800 800  0    60   ~ 0
D0
Text Label 2800 900  0    60   ~ 0
D1
Text Label 2800 1000 0    60   ~ 0
D2
Text Label 2800 1100 0    60   ~ 0
D3
Text Label 2800 1200 0    60   ~ 0
D4
Text Label 2800 1300 0    60   ~ 0
D5
Text Label 2800 1400 0    60   ~ 0
D6
Text Label 2800 1500 0    60   ~ 0
D7
Wire Bus Line
	10800 5900 10800 3600
Wire Wire Line
	10000 3900 10700 3900
Wire Wire Line
	10000 4000 10700 4000
Wire Wire Line
	10000 4100 10700 4100
Wire Wire Line
	10000 4300 10700 4300
Wire Wire Line
	9500 3900 8200 3900
Wire Wire Line
	9500 4000 8200 4000
Wire Wire Line
	9500 4100 8200 4100
Wire Wire Line
	9500 4300 8200 4300
Wire Wire Line
	9500 3800 9400 3800
Wire Wire Line
	9400 1100 9400 5200
Wire Wire Line
	10000 3800 10100 3800
Wire Wire Line
	10100 1100 10100 5200
Wire Wire Line
	9400 4200 9500 4200
Connection ~ 9400 4200
Wire Wire Line
	10000 4200 10100 4200
Connection ~ 10100 4200
$Comp
L GND #PWR01
U 1 1 5E9F72FD
P 9400 5200
F 0 "#PWR01" H 9400 4950 50  0001 C CNN
F 1 "GND" H 9400 5050 50  0000 C CNN
F 2 "" H 9400 5200 50  0001 C CNN
F 3 "" H 9400 5200 50  0001 C CNN
	1    9400 5200
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR02
U 1 1 5E9F7365
P 10100 5200
F 0 "#PWR02" H 10100 4950 50  0001 C CNN
F 1 "GND" H 10100 5050 50  0000 C CNN
F 2 "" H 10100 5200 50  0001 C CNN
F 3 "" H 10100 5200 50  0001 C CNN
	1    10100 5200
	1    0    0    -1  
$EndComp
Wire Wire Line
	9500 1100 9400 1100
Connection ~ 9400 3800
Wire Wire Line
	10000 1100 10100 1100
Connection ~ 10100 3800
Wire Wire Line
	9400 1500 9500 1500
Connection ~ 9400 1500
Wire Wire Line
	10000 1500 10100 1500
Connection ~ 10100 1500
Wire Wire Line
	9400 1900 9500 1900
Connection ~ 9400 1900
Wire Wire Line
	10000 1900 10100 1900
Connection ~ 10100 1900
Wire Wire Line
	9400 2300 9500 2300
Connection ~ 9400 2300
Wire Wire Line
	10000 2300 10100 2300
Connection ~ 10100 2300
Wire Wire Line
	9400 2700 9500 2700
Connection ~ 9400 2700
Wire Wire Line
	10000 2700 10100 2700
Connection ~ 10100 2700
Entry Wire Line
	10700 3900 10800 4000
Entry Wire Line
	10700 4000 10800 4100
Entry Wire Line
	10700 4100 10800 4200
Entry Wire Line
	10700 4300 10800 4400
Entry Wire Line
	8100 4000 8200 3900
Entry Wire Line
	8100 4100 8200 4000
Entry Wire Line
	8100 4200 8200 4100
Entry Wire Line
	8100 4400 8200 4300
Text Label 8900 3900 0    60   ~ 0
D0
Text Label 10600 3900 0    60   ~ 0
D1
Text Label 8900 4000 0    60   ~ 0
D2
Text Label 10600 4000 0    60   ~ 0
D3
Text Label 8900 4100 0    60   ~ 0
D4
Text Label 10600 4100 0    60   ~ 0
D5
Text Label 8900 4300 0    60   ~ 0
D6
Text Label 10600 4300 0    60   ~ 0
D7
Text Notes 9200 3900 0    60   ~ 0
A9
Text Notes 9200 4000 0    60   ~ 0
B8
Text Notes 9200 4100 0    60   ~ 0
B7
Text Notes 9200 4300 0    60   ~ 0
A6
Text Notes 10200 3900 0    60   ~ 0
B9
Text Notes 10200 4000 0    60   ~ 0
A7
Text Notes 10200 4100 0    60   ~ 0
C7
Text Notes 10200 4300 0    60   ~ 0
C6
Text Label 2800 3400 0    60   ~ 0
D0
Text Label 2800 3500 0    60   ~ 0
D1
Text Label 2800 3600 0    60   ~ 0
D2
Text Label 2800 3700 0    60   ~ 0
D3
Text Label 2800 3800 0    60   ~ 0
D4
Text Label 2800 3900 0    60   ~ 0
D5
Text Label 2800 4000 0    60   ~ 0
D6
Text Label 2800 4100 0    60   ~ 0
D7
Text Label 5300 800  0    60   ~ 0
D0
Text Label 5300 900  0    60   ~ 0
D1
Text Label 5300 1000 0    60   ~ 0
D2
Text Label 5300 1100 0    60   ~ 0
D3
Text Label 5300 1200 0    60   ~ 0
D4
Text Label 5300 1300 0    60   ~ 0
D5
Text Label 5300 1400 0    60   ~ 0
D6
Text Label 5300 1500 0    60   ~ 0
D7
Text Label 5300 3400 0    60   ~ 0
D0
Text Label 5300 3500 0    60   ~ 0
D1
Text Label 5300 3600 0    60   ~ 0
D2
Text Label 5300 3700 0    60   ~ 0
D3
Text Label 5300 3800 0    60   ~ 0
D4
Text Label 5300 3900 0    60   ~ 0
D5
Text Label 5300 4000 0    60   ~ 0
D6
Text Label 5300 4100 0    60   ~ 0
D7
Text Label 7800 800  0    60   ~ 0
D0
Text Label 7800 900  0    60   ~ 0
D1
Text Label 7800 1000 0    60   ~ 0
D2
Text Label 7800 1100 0    60   ~ 0
D3
Text Label 7800 1200 0    60   ~ 0
D4
Text Label 7800 1300 0    60   ~ 0
D5
Text Label 7800 1400 0    60   ~ 0
D6
Text Label 7800 1500 0    60   ~ 0
D7
Text Label 7800 3100 0    60   ~ 0
D0
Text Label 7800 3200 0    60   ~ 0
D1
Text Label 7800 3300 0    60   ~ 0
D2
Text Label 7800 3400 0    60   ~ 0
D3
Text Label 7800 3500 0    60   ~ 0
D4
Text Label 7800 3600 0    60   ~ 0
D5
Text Label 7800 3700 0    60   ~ 0
D6
Text Label 7800 3800 0    60   ~ 0
D7
Wire Bus Line
	11100 6000 11100 700 
Wire Bus Line
	8400 700  8400 6000
Wire Bus Line
	600  6000 11100 6000
Wire Wire Line
	9500 1000 8500 1000
Wire Wire Line
	10000 1000 11000 1000
Wire Wire Line
	10000 900  11000 900 
Wire Wire Line
	8500 1200 9500 1200
Wire Wire Line
	8500 1300 9500 1300
Wire Wire Line
	8500 1400 9500 1400
Wire Wire Line
	10000 1200 11000 1200
Wire Wire Line
	10000 1300 11000 1300
Wire Wire Line
	10000 1400 11000 1400
Wire Wire Line
	8500 1600 9500 1600
Wire Wire Line
	8500 1700 9500 1700
Wire Wire Line
	8500 1800 9500 1800
Wire Wire Line
	10000 1600 11000 1600
Wire Wire Line
	10000 1700 11000 1700
Wire Wire Line
	10000 1800 11000 1800
Wire Wire Line
	8500 2100 9500 2100
Wire Wire Line
	8500 2200 9500 2200
Wire Wire Line
	10000 2000 11000 2000
Wire Wire Line
	10000 2100 11000 2100
Wire Wire Line
	10000 2200 11000 2200
NoConn ~ 9500 2000
NoConn ~ 9500 800 
NoConn ~ 9500 900 
Wire Wire Line
	8500 2400 9500 2400
Entry Wire Line
	8400 1100 8500 1000
Entry Wire Line
	8400 1300 8500 1200
Entry Wire Line
	8400 1400 8500 1300
Entry Wire Line
	8400 1500 8500 1400
Entry Wire Line
	8400 1700 8500 1600
Entry Wire Line
	8400 1800 8500 1700
Entry Wire Line
	8400 1900 8500 1800
Entry Wire Line
	8400 2200 8500 2100
Entry Wire Line
	8400 2300 8500 2200
Entry Wire Line
	8400 2500 8500 2400
Entry Wire Line
	11000 900  11100 1000
Entry Wire Line
	11000 1000 11100 1100
Entry Wire Line
	11000 1200 11100 1300
Entry Wire Line
	11000 1300 11100 1400
Entry Wire Line
	11000 1400 11100 1500
Entry Wire Line
	11000 1600 11100 1700
Entry Wire Line
	11000 1700 11100 1800
Entry Wire Line
	11000 1800 11100 1900
Entry Wire Line
	11000 2000 11100 2100
Entry Wire Line
	11000 2100 11100 2200
Entry Wire Line
	11000 2200 11100 2300
Text Label 10600 900  0    60   ~ 0
A0
Text Label 8700 1000 0    60   ~ 0
A1
Text Label 10600 1000 0    60   ~ 0
A2
Text Label 8700 1200 0    60   ~ 0
A3
Text Label 10600 1200 0    60   ~ 0
A4
Text Label 8700 1300 0    60   ~ 0
A5
Text Label 10600 1300 0    60   ~ 0
A6
Text Label 8700 1400 0    60   ~ 0
A7
Text Label 10600 1400 0    60   ~ 0
A8
Text Label 8700 1600 0    60   ~ 0
A9
Text Label 10600 1600 0    60   ~ 0
A10
Text Label 8700 1700 0    60   ~ 0
A11
Text Label 10600 1700 0    60   ~ 0
A12
Text Label 8700 1800 0    60   ~ 0
A13
Text Label 10600 1800 0    60   ~ 0
A14
Text Label 10600 2000 0    60   ~ 0
A15
Text Label 8700 2100 0    60   ~ 0
A16
Text Label 10600 2100 0    60   ~ 0
A17
Text Label 8700 2200 0    60   ~ 0
A18
Text Label 10600 2200 0    60   ~ 0
A19
Text Label 8700 2400 0    60   ~ 0
A20
Text Notes 9200 1000 0    60   ~ 0
P16
Text Notes 9200 1200 0    60   ~ 0
N16
Text Notes 9200 1300 0    60   ~ 0
M16
Text Notes 9200 1400 0    60   ~ 0
K15
Text Notes 9200 1600 0    60   ~ 0
K14
Text Notes 9200 1700 0    60   ~ 0
G14
Text Notes 9200 1800 0    60   ~ 0
J15
Text Notes 9200 2100 0    60   ~ 0
G16
Text Notes 9200 2200 0    60   ~ 0
F16
Text Notes 9200 2400 0    60   ~ 0
E16
Text Notes 9200 2500 0    60   ~ 0
D16
Text Notes 9200 2600 0    60   ~ 0
C16
Text Notes 9200 4400 0    60   ~ 0
B6
Text Notes 9200 4500 0    60   ~ 0
A5
Text Notes 10200 800  0    60   ~ 0
VCCIO1
Text Notes 10200 900  0    60   ~ 0
R15
Text Notes 10200 1000 0    60   ~ 0
P15
Text Notes 10200 1200 0    60   ~ 0
M15
Text Notes 10200 1300 0    60   ~ 0
L16
Text Notes 10200 1400 0    60   ~ 0
K16
Text Notes 10200 1600 0    60   ~ 0
J14
Text Notes 10200 1700 0    60   ~ 0
F14
Text Notes 10200 1800 0    60   ~ 0
H14
Text Notes 10200 2000 0    60   ~ 0
G15
Text Notes 10200 2100 0    60   ~ 0
F15
Text Notes 10200 2200 0    60   ~ 0
E14
Text Notes 10200 2600 0    60   ~ 0
B16
Wire Bus Line
	5700 700  5700 6000
Wire Bus Line
	3200 700  3200 6000
Wire Bus Line
	600  700  600  7500
$Comp
L VCC #PWR03
U 1 1 5EA0A707
P 10100 700
F 0 "#PWR03" H 10100 550 50  0001 C CNN
F 1 "VCC" H 10100 850 50  0000 C CNN
F 2 "" H 10100 700 50  0001 C CNN
F 3 "" H 10100 700 50  0001 C CNN
	1    10100 700 
	1    0    0    -1  
$EndComp
Wire Wire Line
	10000 800  10100 800 
Wire Wire Line
	10100 800  10100 700 
NoConn ~ 10000 3100
Wire Wire Line
	10000 3400 10100 3400
Connection ~ 10100 3400
Wire Wire Line
	9400 3400 9500 3400
Connection ~ 9400 3400
Wire Wire Line
	9400 4600 9500 4600
Connection ~ 9400 4600
Wire Wire Line
	10000 4600 10100 4600
Connection ~ 10100 4600
Wire Wire Line
	9400 5000 9500 5000
Connection ~ 9400 5000
Wire Wire Line
	10000 5000 10100 5000
Connection ~ 10100 5000
Wire Wire Line
	1400 3000 1300 3000
Wire Wire Line
	1300 3000 1300 6100
Wire Wire Line
	1300 5600 1400 5600
Wire Wire Line
	1300 6100 8600 6100
Wire Wire Line
	3800 6100 3800 3000
Wire Wire Line
	3800 5600 3900 5600
Connection ~ 1300 5600
Wire Wire Line
	3800 3000 3900 3000
Connection ~ 3800 5600
Wire Wire Line
	1400 2900 1200 2900
Wire Wire Line
	1200 2900 1200 6200
Wire Wire Line
	1200 6200 8700 6200
Wire Wire Line
	3700 6200 3700 2900
Wire Wire Line
	3700 2900 3900 2900
Wire Wire Line
	3900 5500 3700 5500
Connection ~ 3700 5500
Wire Wire Line
	1400 5500 1200 5500
Connection ~ 1200 5500
Wire Wire Line
	6200 6200 6200 2600
Wire Wire Line
	6200 2600 6400 2600
Connection ~ 3700 6200
Wire Wire Line
	6400 4900 6200 4900
Connection ~ 6200 4900
Wire Wire Line
	6400 2700 6300 2700
Wire Wire Line
	6300 2700 6300 5300
Wire Wire Line
	6300 5000 6400 5000
$Sheet
S 1200 6500 1300 1000
U 5EA0D14A
F0 "Demux" 60
F1 "demux.sch" 60
F2 "A19" I L 1200 7200 60 
F3 "A20" I L 1200 7300 60 
F4 "~CS0" O L 1200 6700 60 
F5 "~CS1" O L 1200 6800 60 
F6 "~CS2" O R 2500 6700 60 
F7 "~CS3" O R 2500 6800 60 
F8 "~CSROM" I R 2500 7300 60 
$EndSheet
Wire Wire Line
	700  7300 1200 7300
Wire Wire Line
	700  7200 1200 7200
Entry Wire Line
	600  7300 700  7200
Entry Wire Line
	600  7400 700  7300
Text Label 700  7200 0    60   ~ 0
A19
Text Label 700  7300 0    60   ~ 0
A20
Wire Wire Line
	1400 2800 1000 2800
Wire Wire Line
	1400 5400 1100 5400
Wire Wire Line
	3900 2800 3600 2800
Wire Wire Line
	3600 2800 3600 6700
Wire Wire Line
	3900 5400 3500 5400
Wire Wire Line
	3500 5400 3500 6800
Wire Wire Line
	3300 5200 3900 5200
Wire Wire Line
	3300 5100 3900 5100
Wire Wire Line
	3300 5000 3900 5000
Wire Wire Line
	3300 4900 3900 4900
Wire Wire Line
	3300 4800 3900 4800
Wire Wire Line
	3300 4700 3900 4700
Wire Wire Line
	3300 4600 3900 4600
Wire Wire Line
	3300 4500 3900 4500
Wire Wire Line
	3300 4400 3900 4400
Wire Wire Line
	3300 4300 3900 4300
Wire Wire Line
	3300 4200 3900 4200
Wire Wire Line
	3300 4100 3900 4100
Wire Wire Line
	3300 4000 3900 4000
Wire Wire Line
	3300 3900 3900 3900
Wire Wire Line
	3300 3800 3900 3800
Wire Wire Line
	3300 3700 3900 3700
Wire Wire Line
	3300 3600 3900 3600
Wire Wire Line
	3300 3500 3900 3500
Wire Wire Line
	3300 3400 3900 3400
Entry Wire Line
	3200 3500 3300 3400
Entry Wire Line
	3200 3600 3300 3500
Entry Wire Line
	3200 3700 3300 3600
Entry Wire Line
	3200 3800 3300 3700
Entry Wire Line
	3200 3900 3300 3800
Entry Wire Line
	3200 4000 3300 3900
Entry Wire Line
	3200 4100 3300 4000
Entry Wire Line
	3200 4200 3300 4100
Entry Wire Line
	3200 4300 3300 4200
Entry Wire Line
	3200 4400 3300 4300
Entry Wire Line
	3200 4500 3300 4400
Entry Wire Line
	3200 4600 3300 4500
Entry Wire Line
	3200 4700 3300 4600
Entry Wire Line
	3200 4800 3300 4700
Entry Wire Line
	3200 4900 3300 4800
Entry Wire Line
	3200 5000 3300 4900
Entry Wire Line
	3200 5100 3300 5000
Entry Wire Line
	3200 5200 3300 5100
Entry Wire Line
	3200 5300 3300 5200
Wire Wire Line
	1000 2800 1000 6700
Wire Wire Line
	1000 6700 1200 6700
Wire Wire Line
	1100 5400 1100 6800
Wire Wire Line
	1100 6800 1200 6800
Wire Wire Line
	3600 6700 2500 6700
Wire Wire Line
	3500 6800 2500 6800
$Comp
L C C1
U 1 1 5EA17BB9
P 4400 7250
F 0 "C1" H 4425 7350 50  0000 L CNN
F 1 "100n" H 4425 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 4438 7100 50  0001 C CNN
F 3 "" H 4400 7250 50  0001 C CNN
	1    4400 7250
	1    0    0    -1  
$EndComp
$Comp
L C C2
U 1 1 5EA17C86
P 4800 7250
F 0 "C2" H 4825 7350 50  0000 L CNN
F 1 "100n" H 4825 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 4838 7100 50  0001 C CNN
F 3 "" H 4800 7250 50  0001 C CNN
	1    4800 7250
	1    0    0    -1  
$EndComp
$Comp
L C C3
U 1 1 5EA17D19
P 5200 7250
F 0 "C3" H 5225 7350 50  0000 L CNN
F 1 "100n" H 5225 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 5238 7100 50  0001 C CNN
F 3 "" H 5200 7250 50  0001 C CNN
	1    5200 7250
	1    0    0    -1  
$EndComp
$Comp
L C C4
U 1 1 5EA17DB4
P 5600 7250
F 0 "C4" H 5625 7350 50  0000 L CNN
F 1 "100n" H 5625 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 5638 7100 50  0001 C CNN
F 3 "" H 5600 7250 50  0001 C CNN
	1    5600 7250
	1    0    0    -1  
$EndComp
$Comp
L C C5
U 1 1 5EA17E43
P 6000 7250
F 0 "C5" H 6025 7350 50  0000 L CNN
F 1 "100n" H 6025 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 6038 7100 50  0001 C CNN
F 3 "" H 6000 7250 50  0001 C CNN
	1    6000 7250
	1    0    0    -1  
$EndComp
$Comp
L C C6
U 1 1 5EA17EC2
P 6400 7250
F 0 "C6" H 6425 7350 50  0000 L CNN
F 1 "100n" H 6425 7150 50  0000 L CNN
F 2 "Capacitors_THT:C_Disc_D3.0mm_W2.0mm_P2.50mm" H 6438 7100 50  0001 C CNN
F 3 "" H 6400 7250 50  0001 C CNN
	1    6400 7250
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR04
U 1 1 5EA17F5B
P 4400 7500
F 0 "#PWR04" H 4400 7250 50  0001 C CNN
F 1 "GND" H 4400 7350 50  0000 C CNN
F 2 "" H 4400 7500 50  0001 C CNN
F 3 "" H 4400 7500 50  0001 C CNN
	1    4400 7500
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR05
U 1 1 5EA17FB5
P 4800 7500
F 0 "#PWR05" H 4800 7250 50  0001 C CNN
F 1 "GND" H 4800 7350 50  0000 C CNN
F 2 "" H 4800 7500 50  0001 C CNN
F 3 "" H 4800 7500 50  0001 C CNN
	1    4800 7500
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR06
U 1 1 5EA1800F
P 5200 7500
F 0 "#PWR06" H 5200 7250 50  0001 C CNN
F 1 "GND" H 5200 7350 50  0000 C CNN
F 2 "" H 5200 7500 50  0001 C CNN
F 3 "" H 5200 7500 50  0001 C CNN
	1    5200 7500
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR07
U 1 1 5EA18069
P 5600 7500
F 0 "#PWR07" H 5600 7250 50  0001 C CNN
F 1 "GND" H 5600 7350 50  0000 C CNN
F 2 "" H 5600 7500 50  0001 C CNN
F 3 "" H 5600 7500 50  0001 C CNN
	1    5600 7500
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR08
U 1 1 5EA180C3
P 6000 7500
F 0 "#PWR08" H 6000 7250 50  0001 C CNN
F 1 "GND" H 6000 7350 50  0000 C CNN
F 2 "" H 6000 7500 50  0001 C CNN
F 3 "" H 6000 7500 50  0001 C CNN
	1    6000 7500
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR09
U 1 1 5EA1811D
P 6400 7500
F 0 "#PWR09" H 6400 7250 50  0001 C CNN
F 1 "GND" H 6400 7350 50  0000 C CNN
F 2 "" H 6400 7500 50  0001 C CNN
F 3 "" H 6400 7500 50  0001 C CNN
	1    6400 7500
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR010
U 1 1 5EA18177
P 4400 7000
F 0 "#PWR010" H 4400 6850 50  0001 C CNN
F 1 "VCC" H 4400 7150 50  0000 C CNN
F 2 "" H 4400 7000 50  0001 C CNN
F 3 "" H 4400 7000 50  0001 C CNN
	1    4400 7000
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR011
U 1 1 5EA181D1
P 4800 7000
F 0 "#PWR011" H 4800 6850 50  0001 C CNN
F 1 "VCC" H 4800 7150 50  0000 C CNN
F 2 "" H 4800 7000 50  0001 C CNN
F 3 "" H 4800 7000 50  0001 C CNN
	1    4800 7000
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR012
U 1 1 5EA1822B
P 5200 7000
F 0 "#PWR012" H 5200 6850 50  0001 C CNN
F 1 "VCC" H 5200 7150 50  0000 C CNN
F 2 "" H 5200 7000 50  0001 C CNN
F 3 "" H 5200 7000 50  0001 C CNN
	1    5200 7000
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR013
U 1 1 5EA18285
P 5600 7000
F 0 "#PWR013" H 5600 6850 50  0001 C CNN
F 1 "VCC" H 5600 7150 50  0000 C CNN
F 2 "" H 5600 7000 50  0001 C CNN
F 3 "" H 5600 7000 50  0001 C CNN
	1    5600 7000
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR014
U 1 1 5EA182DF
P 6000 7000
F 0 "#PWR014" H 6000 6850 50  0001 C CNN
F 1 "VCC" H 6000 7150 50  0000 C CNN
F 2 "" H 6000 7000 50  0001 C CNN
F 3 "" H 6000 7000 50  0001 C CNN
	1    6000 7000
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR015
U 1 1 5EA18339
P 6400 7000
F 0 "#PWR015" H 6400 6850 50  0001 C CNN
F 1 "VCC" H 6400 7150 50  0000 C CNN
F 2 "" H 6400 7000 50  0001 C CNN
F 3 "" H 6400 7000 50  0001 C CNN
	1    6400 7000
	1    0    0    -1  
$EndComp
Wire Wire Line
	4400 7000 4400 7100
Wire Wire Line
	4800 7100 4800 7000
Wire Wire Line
	5200 7000 5200 7100
Wire Wire Line
	5600 7100 5600 7000
Wire Wire Line
	6000 7000 6000 7100
Wire Wire Line
	6400 7100 6400 7000
Wire Wire Line
	6400 7400 6400 7500
Wire Wire Line
	6000 7500 6000 7400
Wire Wire Line
	5600 7400 5600 7500
Wire Wire Line
	5200 7500 5200 7400
Wire Wire Line
	4800 7400 4800 7500
Wire Wire Line
	4400 7500 4400 7400
NoConn ~ 10000 3600
NoConn ~ 9500 4900
NoConn ~ 10000 4900
NoConn ~ 10000 4800
NoConn ~ 10000 4700
NoConn ~ 9500 4800
NoConn ~ 9500 4700
NoConn ~ 10000 4500
NoConn ~ 10000 4400
NoConn ~ 9500 3500
NoConn ~ 10000 3300
NoConn ~ 10000 3200
NoConn ~ 9500 3100
NoConn ~ 9500 3200
NoConn ~ 9500 3300
Text Notes 9200 3700 0    60   ~ 0
A10
Wire Wire Line
	8600 6100 8600 3700
Wire Wire Line
	8600 3700 9500 3700
Connection ~ 3800 6100
Text Label 8900 3700 0    60   ~ 0
~PROG
Wire Wire Line
	6400 2500 6100 2500
Wire Wire Line
	6100 2500 6100 2900
Wire Wire Line
	6100 2900 8600 2900
Wire Wire Line
	8600 2900 8600 2500
Wire Wire Line
	8600 2500 9500 2500
Text Label 8700 2500 0    60   ~ 0
~CSWRAM
Wire Wire Line
	6400 4800 6100 4800
Wire Wire Line
	6100 4800 6100 5200
Wire Wire Line
	6100 5200 8500 5200
Wire Wire Line
	8500 5200 8500 2600
Wire Wire Line
	8500 2600 9500 2600
Text Label 8700 2600 0    60   ~ 0
~CSXRAM
Wire Wire Line
	8700 6200 8700 4400
Wire Wire Line
	8700 4400 9500 4400
Connection ~ 6200 6200
Wire Wire Line
	6300 5300 8800 5300
Wire Wire Line
	8800 5300 8800 4500
Wire Wire Line
	8800 4500 9500 4500
Connection ~ 6300 5000
Text Label 8900 4400 0    60   ~ 0
~RD
Text Label 8900 4500 0    60   ~ 0
~WR
Wire Wire Line
	2500 7300 3700 7300
Wire Wire Line
	3700 6300 3700 7500
Wire Wire Line
	3700 6300 10900 6300
Wire Wire Line
	10900 6300 10900 2600
Wire Wire Line
	10900 2600 10000 2600
Text Label 10600 2600 0    60   ~ 0
~CSROM
NoConn ~ 10000 2400
NoConn ~ 10000 2500
NoConn ~ 10000 3500
NoConn ~ 10000 3700
NoConn ~ 9500 3600
Wire Wire Line
	700  3400 1400 3400
Wire Wire Line
	700  3500 1400 3500
Wire Wire Line
	700  3600 1400 3600
Wire Wire Line
	700  3700 1400 3700
Wire Wire Line
	700  3800 1400 3800
Wire Wire Line
	700  3900 1400 3900
Wire Wire Line
	700  4000 1400 4000
Wire Wire Line
	700  4100 1400 4100
Wire Wire Line
	700  4200 1400 4200
Wire Wire Line
	700  4300 1400 4300
Wire Wire Line
	700  4400 1400 4400
Wire Wire Line
	700  4500 1400 4500
Wire Wire Line
	700  4600 1400 4600
Wire Wire Line
	700  4700 1400 4700
Wire Wire Line
	700  4800 1400 4800
Wire Wire Line
	700  4900 1400 4900
Wire Wire Line
	700  5000 1400 5000
Wire Wire Line
	700  5100 1400 5100
Wire Wire Line
	700  5200 1400 5200
Wire Wire Line
	700  800  1400 800 
Wire Wire Line
	700  900  1400 900 
Wire Wire Line
	700  1000 1400 1000
Wire Wire Line
	700  1100 1400 1100
Wire Wire Line
	700  1200 1400 1200
Wire Wire Line
	700  1300 1400 1300
Wire Wire Line
	700  1400 1400 1400
Wire Wire Line
	700  1500 1400 1500
Wire Wire Line
	700  1600 1400 1600
Wire Wire Line
	700  1700 1400 1700
Wire Wire Line
	700  1800 1400 1800
Wire Wire Line
	700  1900 1400 1900
Wire Wire Line
	700  2000 1400 2000
Wire Wire Line
	700  2100 1400 2100
Wire Wire Line
	700  2200 1400 2200
Wire Wire Line
	700  2300 1400 2300
Wire Wire Line
	700  2400 1400 2400
Wire Wire Line
	700  2500 1400 2500
Wire Wire Line
	700  2600 1400 2600
Wire Wire Line
	3300 800  3900 800 
Wire Wire Line
	3300 900  3900 900 
Wire Wire Line
	3300 1000 3900 1000
Wire Wire Line
	3300 1100 3900 1100
Wire Wire Line
	3300 1200 3900 1200
Wire Wire Line
	3300 1300 3900 1300
Wire Wire Line
	3300 1400 3900 1400
Wire Wire Line
	3300 1500 3900 1500
Wire Wire Line
	3300 1600 3900 1600
Wire Wire Line
	3300 1700 3900 1700
Wire Wire Line
	3300 1800 3900 1800
Wire Wire Line
	3300 1900 3900 1900
Wire Wire Line
	3300 2000 3900 2000
Wire Wire Line
	3300 2100 3900 2100
Wire Wire Line
	3300 2200 3900 2200
Wire Wire Line
	3300 2300 3900 2300
Wire Wire Line
	3300 2400 3900 2400
Wire Wire Line
	3300 2500 3900 2500
Wire Wire Line
	3300 2600 3900 2600
Wire Wire Line
	5800 800  6400 800 
Wire Wire Line
	5800 900  6400 900 
Wire Wire Line
	5800 1000 6400 1000
Wire Wire Line
	5800 1100 6400 1100
Wire Wire Line
	5800 1200 6400 1200
Wire Wire Line
	5800 1300 6400 1300
Wire Wire Line
	5800 1400 6400 1400
Wire Wire Line
	5800 1500 6400 1500
Wire Wire Line
	5800 1600 6400 1600
Wire Wire Line
	5800 1700 6400 1700
Wire Wire Line
	5800 1800 6400 1800
Wire Wire Line
	5800 1900 6400 1900
Wire Wire Line
	5800 2000 6400 2000
Wire Wire Line
	5800 2100 6400 2100
Wire Wire Line
	5800 2200 6400 2200
Wire Wire Line
	5800 3100 6400 3100
Wire Wire Line
	5800 3200 6400 3200
Wire Wire Line
	5800 3300 6400 3300
Wire Wire Line
	5800 3400 6400 3400
Wire Wire Line
	5800 3500 6400 3500
Wire Wire Line
	5800 3600 6400 3600
Wire Wire Line
	5800 3700 6400 3700
Wire Wire Line
	5800 3800 6400 3800
Wire Wire Line
	5800 3900 6400 3900
Wire Wire Line
	5800 4000 6400 4000
Wire Wire Line
	5800 4100 6400 4100
Wire Wire Line
	5800 4200 6400 4200
Wire Wire Line
	5800 4300 6400 4300
Wire Wire Line
	5800 4400 6400 4400
Wire Wire Line
	5800 4500 6400 4500
Entry Wire Line
	600  900  700  800 
Entry Wire Line
	600  1000 700  900 
Entry Wire Line
	600  1100 700  1000
Entry Wire Line
	600  1200 700  1100
Entry Wire Line
	600  1300 700  1200
Entry Wire Line
	600  1400 700  1300
Entry Wire Line
	600  1500 700  1400
Entry Wire Line
	600  1600 700  1500
Entry Wire Line
	600  1700 700  1600
Entry Wire Line
	600  1800 700  1700
Entry Wire Line
	600  1900 700  1800
Entry Wire Line
	600  2000 700  1900
Entry Wire Line
	600  2100 700  2000
Entry Wire Line
	600  2200 700  2100
Entry Wire Line
	600  2300 700  2200
Entry Wire Line
	600  2400 700  2300
Entry Wire Line
	600  2500 700  2400
Entry Wire Line
	600  2600 700  2500
Entry Wire Line
	600  2700 700  2600
Entry Wire Line
	600  3500 700  3400
Entry Wire Line
	600  3600 700  3500
Entry Wire Line
	600  3700 700  3600
Entry Wire Line
	600  3800 700  3700
Entry Wire Line
	600  3900 700  3800
Entry Wire Line
	600  4000 700  3900
Entry Wire Line
	600  4100 700  4000
Entry Wire Line
	600  4200 700  4100
Entry Wire Line
	600  4300 700  4200
Entry Wire Line
	600  4400 700  4300
Entry Wire Line
	600  4500 700  4400
Entry Wire Line
	600  4600 700  4500
Entry Wire Line
	600  4700 700  4600
Entry Wire Line
	600  4800 700  4700
Entry Wire Line
	600  4900 700  4800
Entry Wire Line
	600  5000 700  4900
Entry Wire Line
	600  5100 700  5000
Entry Wire Line
	600  5200 700  5100
Entry Wire Line
	600  5300 700  5200
Entry Wire Line
	3200 900  3300 800 
Entry Wire Line
	3200 1000 3300 900 
Entry Wire Line
	3200 1100 3300 1000
Entry Wire Line
	3200 1200 3300 1100
Entry Wire Line
	3200 1300 3300 1200
Entry Wire Line
	3200 1400 3300 1300
Entry Wire Line
	3200 1500 3300 1400
Entry Wire Line
	3200 1600 3300 1500
Entry Wire Line
	3200 1700 3300 1600
Entry Wire Line
	3200 1800 3300 1700
Entry Wire Line
	3200 1900 3300 1800
Entry Wire Line
	3200 2000 3300 1900
Entry Wire Line
	3200 2100 3300 2000
Entry Wire Line
	3200 2200 3300 2100
Entry Wire Line
	3200 2300 3300 2200
Entry Wire Line
	3200 2400 3300 2300
Entry Wire Line
	3200 2500 3300 2400
Entry Wire Line
	3200 2600 3300 2500
Entry Wire Line
	3200 2700 3300 2600
Entry Wire Line
	5700 900  5800 800 
Entry Wire Line
	5700 1000 5800 900 
Entry Wire Line
	5700 1100 5800 1000
Entry Wire Line
	5700 1200 5800 1100
Entry Wire Line
	5700 1300 5800 1200
Entry Wire Line
	5700 1400 5800 1300
Entry Wire Line
	5700 1500 5800 1400
Entry Wire Line
	5700 1600 5800 1500
Entry Wire Line
	5700 1700 5800 1600
Entry Wire Line
	5700 1800 5800 1700
Entry Wire Line
	5700 1900 5800 1800
Entry Wire Line
	5700 2000 5800 1900
Entry Wire Line
	5700 2100 5800 2000
Entry Wire Line
	5700 2200 5800 2100
Entry Wire Line
	5700 2300 5800 2200
Entry Wire Line
	5700 3200 5800 3100
Entry Wire Line
	5700 3300 5800 3200
Entry Wire Line
	5700 3400 5800 3300
Entry Wire Line
	5700 3500 5800 3400
Entry Wire Line
	5700 3600 5800 3500
Entry Wire Line
	5700 3700 5800 3600
Entry Wire Line
	5700 3800 5800 3700
Entry Wire Line
	5700 3900 5800 3800
Entry Wire Line
	5700 4000 5800 3900
Entry Wire Line
	5700 4100 5800 4000
Entry Wire Line
	5700 4200 5800 4100
Entry Wire Line
	5700 4300 5800 4200
Entry Wire Line
	5700 4400 5800 4300
Entry Wire Line
	5700 4500 5800 4400
Entry Wire Line
	5700 4600 5800 4500
Text Label 700  800  0    60   ~ 0
A0
Text Label 700  900  0    60   ~ 0
A1
Text Label 700  1000 0    60   ~ 0
A2
Text Label 700  1100 0    60   ~ 0
A3
Text Label 700  1200 0    60   ~ 0
A4
Text Label 700  1300 0    60   ~ 0
A5
Text Label 700  1400 0    60   ~ 0
A6
Text Label 700  1500 0    60   ~ 0
A7
Text Label 700  1600 0    60   ~ 0
A8
Text Label 700  1700 0    60   ~ 0
A9
Text Label 700  1800 0    60   ~ 0
A10
Text Label 700  1900 0    60   ~ 0
A11
Text Label 700  2000 0    60   ~ 0
A12
Text Label 700  2100 0    60   ~ 0
A13
Text Label 700  2200 0    60   ~ 0
A14
Text Label 700  2300 0    60   ~ 0
A15
Text Label 700  2400 0    60   ~ 0
A16
Text Label 700  2500 0    60   ~ 0
A17
Text Label 700  2600 0    60   ~ 0
A18
$Comp
L R R2
U 1 1 5EA42FCE
P 7800 2350
F 0 "R2" V 7880 2350 50  0000 C CNN
F 1 "10k" V 7800 2350 50  0000 C CNN
F 2 "Resistors_THT:R_Axial_DIN0207_L6.3mm_D2.5mm_P10.16mm_Horizontal" V 7730 2350 50  0001 C CNN
F 3 "" H 7800 2350 50  0001 C CNN
	1    7800 2350
	1    0    0    -1  
$EndComp
Wire Wire Line
	7800 2500 7800 2900
Connection ~ 7800 2900
$Comp
L VCC #PWR016
U 1 1 5EA43C05
P 7800 2100
F 0 "#PWR016" H 7800 1950 50  0001 C CNN
F 1 "VCC" H 7800 2250 50  0000 C CNN
F 2 "" H 7800 2100 50  0001 C CNN
F 3 "" H 7800 2100 50  0001 C CNN
	1    7800 2100
	1    0    0    -1  
$EndComp
Wire Wire Line
	7800 2200 7800 2100
$Comp
L R R3
U 1 1 5EA4425D
P 7800 4650
F 0 "R3" V 7880 4650 50  0000 C CNN
F 1 "10k" V 7800 4650 50  0000 C CNN
F 2 "Resistors_THT:R_Axial_DIN0207_L6.3mm_D2.5mm_P10.16mm_Horizontal" V 7730 4650 50  0001 C CNN
F 3 "" H 7800 4650 50  0001 C CNN
	1    7800 4650
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR017
U 1 1 5EA443FA
P 7800 4400
F 0 "#PWR017" H 7800 4250 50  0001 C CNN
F 1 "VCC" H 7800 4550 50  0000 C CNN
F 2 "" H 7800 4400 50  0001 C CNN
F 3 "" H 7800 4400 50  0001 C CNN
	1    7800 4400
	1    0    0    -1  
$EndComp
Wire Wire Line
	7800 5200 7800 4800
Connection ~ 7800 5200
Wire Wire Line
	7800 4500 7800 4400
$Comp
L R R1
U 1 1 5EA454AE
P 4000 7250
F 0 "R1" V 4080 7250 50  0000 C CNN
F 1 "10k" V 4000 7250 50  0000 C CNN
F 2 "Resistors_THT:R_Axial_DIN0207_L6.3mm_D2.5mm_P10.16mm_Horizontal" V 3930 7250 50  0001 C CNN
F 3 "" H 4000 7250 50  0001 C CNN
	1    4000 7250
	1    0    0    -1  
$EndComp
Wire Wire Line
	3700 7500 4000 7500
Wire Wire Line
	4000 7500 4000 7400
Connection ~ 3700 7300
Wire Wire Line
	4000 7000 4000 7100
$Comp
L VCC #PWR018
U 1 1 5EA45879
P 4000 7000
F 0 "#PWR018" H 4000 6850 50  0001 C CNN
F 1 "VCC" H 4000 7150 50  0000 C CNN
F 2 "" H 4000 7000 50  0001 C CNN
F 3 "" H 4000 7000 50  0001 C CNN
	1    4000 7000
	1    0    0    -1  
$EndComp
Text Label 700  3400 0    60   ~ 0
A0
Text Label 700  3500 0    60   ~ 0
A1
Text Label 700  3600 0    60   ~ 0
A2
Text Label 700  3700 0    60   ~ 0
A3
Text Label 700  3800 0    60   ~ 0
A4
Text Label 700  3900 0    60   ~ 0
A5
Text Label 700  4000 0    60   ~ 0
A6
Text Label 700  4100 0    60   ~ 0
A7
Text Label 700  4200 0    60   ~ 0
A8
Text Label 700  4300 0    60   ~ 0
A9
Text Label 700  4400 0    60   ~ 0
A10
Text Label 700  4500 0    60   ~ 0
A11
Text Label 700  4600 0    60   ~ 0
A12
Text Label 700  4700 0    60   ~ 0
A13
Text Label 700  4800 0    60   ~ 0
A14
Text Label 700  4900 0    60   ~ 0
A15
Text Label 700  5000 0    60   ~ 0
A16
Text Label 700  5100 0    60   ~ 0
A17
Text Label 700  5200 0    60   ~ 0
A18
Text Label 3300 800  0    60   ~ 0
A0
Text Label 3300 900  0    60   ~ 0
A1
Text Label 3300 1000 0    60   ~ 0
A2
Text Label 3300 1100 0    60   ~ 0
A3
Text Label 3300 1200 0    60   ~ 0
A4
Text Label 3300 1300 0    60   ~ 0
A5
Text Label 3300 1400 0    60   ~ 0
A6
Text Label 3300 1500 0    60   ~ 0
A7
Text Label 3300 1600 0    60   ~ 0
A8
Text Label 3300 1700 0    60   ~ 0
A9
Text Label 3300 1800 0    60   ~ 0
A10
Text Label 3300 1900 0    60   ~ 0
A11
Text Label 3300 2000 0    60   ~ 0
A12
Text Label 3300 2100 0    60   ~ 0
A13
Text Label 3300 2200 0    60   ~ 0
A14
Text Label 3300 2300 0    60   ~ 0
A15
Text Label 3300 2400 0    60   ~ 0
A16
Text Label 3300 2500 0    60   ~ 0
A17
Text Label 3300 2600 0    60   ~ 0
A18
Text Label 3300 3400 0    60   ~ 0
A0
Text Label 3300 3500 0    60   ~ 0
A1
Text Label 3300 3600 0    60   ~ 0
A2
Text Label 3300 3700 0    60   ~ 0
A3
Text Label 3300 3800 0    60   ~ 0
A4
Text Label 3300 3900 0    60   ~ 0
A5
Text Label 3300 4000 0    60   ~ 0
A6
Text Label 3300 4100 0    60   ~ 0
A7
Text Label 3300 4200 0    60   ~ 0
A8
Text Label 3300 4300 0    60   ~ 0
A9
Text Label 3300 4400 0    60   ~ 0
A10
Text Label 3300 4500 0    60   ~ 0
A11
Text Label 3300 4600 0    60   ~ 0
A12
Text Label 3300 4700 0    60   ~ 0
A13
Text Label 3300 4800 0    60   ~ 0
A14
Text Label 3300 4900 0    60   ~ 0
A15
Text Label 3300 5000 0    60   ~ 0
A16
Text Label 3300 5100 0    60   ~ 0
A17
Text Label 3300 5200 0    60   ~ 0
A18
Text Label 5800 800  0    60   ~ 0
A0
Text Label 5800 900  0    60   ~ 0
A1
Text Label 5800 1000 0    60   ~ 0
A2
Text Label 5800 1100 0    60   ~ 0
A3
Text Label 5800 1200 0    60   ~ 0
A4
Text Label 5800 1300 0    60   ~ 0
A5
Text Label 5800 1400 0    60   ~ 0
A6
Text Label 5800 1500 0    60   ~ 0
A7
Text Label 5800 1600 0    60   ~ 0
A8
Text Label 5800 1700 0    60   ~ 0
A9
Text Label 5800 1800 0    60   ~ 0
A10
Text Label 5800 1900 0    60   ~ 0
A11
Text Label 5800 2000 0    60   ~ 0
A12
Text Label 5800 3100 0    60   ~ 0
A0
Text Label 5800 3200 0    60   ~ 0
A1
Text Label 5800 3300 0    60   ~ 0
A2
Text Label 5800 3400 0    60   ~ 0
A3
Text Label 5800 3500 0    60   ~ 0
A4
Text Label 5800 3600 0    60   ~ 0
A5
Text Label 5800 3700 0    60   ~ 0
A6
Text Label 5800 3800 0    60   ~ 0
A7
Text Label 5800 3900 0    60   ~ 0
A8
Text Label 5800 4000 0    60   ~ 0
A9
Text Label 5800 4100 0    60   ~ 0
A10
Text Label 5800 4200 0    60   ~ 0
A11
Text Label 5800 4300 0    60   ~ 0
A12
Text Label 5800 2100 0    60   ~ 0
A13
Text Label 5800 2200 0    60   ~ 0
A14
Text Label 5800 4400 0    60   ~ 0
A13
Text Label 5800 4500 0    60   ~ 0
A14
$Comp
L PWR_FLAG #FLG019
U 1 1 5EA52D7B
P 6750 7000
F 0 "#FLG019" H 6750 7075 50  0001 C CNN
F 1 "PWR_FLAG" H 6750 7150 50  0000 C CNN
F 2 "" H 6750 7000 50  0001 C CNN
F 3 "" H 6750 7000 50  0001 C CNN
	1    6750 7000
	1    0    0    -1  
$EndComp
Wire Wire Line
	6400 7000 6750 7000
Connection ~ 6400 7000
$Comp
L PWR_FLAG #FLG020
U 1 1 5EA54436
P 6750 7500
F 0 "#FLG020" H 6750 7575 50  0001 C CNN
F 1 "PWR_FLAG" H 6750 7650 50  0000 C CNN
F 2 "" H 6750 7500 50  0001 C CNN
F 3 "" H 6750 7500 50  0001 C CNN
	1    6750 7500
	-1   0    0    1   
$EndComp
Wire Wire Line
	6400 7500 6750 7500
Connection ~ 6400 7500
$EndSCHEMATC
