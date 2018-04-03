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
EELAYER 25 0
EELAYER END
$Descr A4 11693 8268
encoding utf-8
Sheet 1 1
Title "IceBoy Memory"
Date "2018-04-04"
Rev ""
Comp ""
Comment1 ""
Comment2 ""
Comment3 ""
Comment4 ""
$EndDescr
$Comp
L 74HC04 U6
U 1 1 5AC3D4B1
P 1500 4800
F 0 "U6" H 1650 4900 50  0000 C CNN
F 1 "74HC04" H 1700 4700 50  0000 C CNN
F 2 "" H 1500 4800 50  0001 C CNN
F 3 "" H 1500 4800 50  0001 C CNN
	1    1500 4800
	1    0    0    -1  
$EndComp
$Comp
L 74HC32 U5
U 1 1 5AC3E4F1
P 1550 5600
F 0 "U5" H 1550 5650 50  0000 C CNN
F 1 "74HC32" H 1600 5550 50  0000 C CNN
F 2 "" H 1550 5600 50  0001 C CNN
F 3 "" H 1550 5600 50  0001 C CNN
	1    1550 5600
	1    0    0    -1  
$EndComp
$Comp
L 74HC32 U5
U 2 1 5AC3E566
P 1550 6100
F 0 "U5" H 1550 6150 50  0000 C CNN
F 1 "74HC32" H 1600 6050 50  0000 C CNN
F 2 "" H 1550 6100 50  0001 C CNN
F 3 "" H 1550 6100 50  0001 C CNN
	2    1550 6100
	1    0    0    -1  
$EndComp
$Comp
L CONN_02X20 J2
U 1 1 5AC3E5BB
P 9700 2400
F 0 "J2" H 9700 3450 50  0000 C CNN
F 1 "CONN_02X20" V 9700 2400 50  0000 C CNN
F 2 "" H 9700 1450 50  0001 C CNN
F 3 "" H 9700 1450 50  0001 C CNN
	1    9700 2400
	1    0    0    -1  
$EndComp
$Comp
L CONN_02X20 J1
U 1 1 5AC3E628
P 9700 4800
F 0 "J1" H 9700 5850 50  0000 C CNN
F 1 "CONN_02X20" V 9700 4800 50  0000 C CNN
F 2 "" H 9700 3850 50  0001 C CNN
F 3 "" H 9700 3850 50  0001 C CNN
	1    9700 4800
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR?
U 1 1 5AC3E973
P 10100 1250
F 0 "#PWR?" H 10100 1100 50  0001 C CNN
F 1 "VCC" H 10100 1400 50  0000 C CNN
F 2 "" H 10100 1250 50  0001 C CNN
F 3 "" H 10100 1250 50  0001 C CNN
	1    10100 1250
	1    0    0    -1  
$EndComp
NoConn ~ 9450 1450
NoConn ~ 9450 1550
NoConn ~ 9950 3850
NoConn ~ 9950 3950
NoConn ~ 9950 4050
NoConn ~ 9950 4150
NoConn ~ 9950 4250
NoConn ~ 9450 3850
NoConn ~ 9450 3950
NoConn ~ 9450 4050
NoConn ~ 9450 4150
NoConn ~ 9450 4250
NoConn ~ 9950 5750
NoConn ~ 9950 5650
NoConn ~ 9950 5550
NoConn ~ 9950 5450
NoConn ~ 9950 5350
NoConn ~ 9450 5750
NoConn ~ 9450 5650
NoConn ~ 9450 5550
NoConn ~ 9450 5450
NoConn ~ 9450 5350
NoConn ~ 9950 5250
NoConn ~ 9950 5150
NoConn ~ 9950 4350
NoConn ~ 9950 4450
NoConn ~ 9450 4450
$Comp
L GND #PWR?
U 1 1 5AC3EEBF
P 10100 3450
F 0 "#PWR?" H 10100 3200 50  0001 C CNN
F 1 "GND" H 10100 3300 50  0000 C CNN
F 2 "" H 10100 3450 50  0001 C CNN
F 3 "" H 10100 3450 50  0001 C CNN
	1    10100 3450
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR?
U 1 1 5AC3EEDD
P 9300 3450
F 0 "#PWR?" H 9300 3200 50  0001 C CNN
F 1 "GND" H 9300 3300 50  0000 C CNN
F 2 "" H 9300 3450 50  0001 C CNN
F 3 "" H 9300 3450 50  0001 C CNN
	1    9300 3450
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR?
U 1 1 5AC3F063
P 10100 5900
F 0 "#PWR?" H 10100 5650 50  0001 C CNN
F 1 "GND" H 10100 5750 50  0000 C CNN
F 2 "" H 10100 5900 50  0001 C CNN
F 3 "" H 10100 5900 50  0001 C CNN
	1    10100 5900
	1    0    0    -1  
$EndComp
$Comp
L GND #PWR?
U 1 1 5AC3F081
P 9300 5900
F 0 "#PWR?" H 9300 5650 50  0001 C CNN
F 1 "GND" H 9300 5750 50  0000 C CNN
F 2 "" H 9300 5900 50  0001 C CNN
F 3 "" H 9300 5900 50  0001 C CNN
	1    9300 5900
	1    0    0    -1  
$EndComp
Entry Wire Line
	11000 1550 11100 1650
Entry Wire Line
	11000 1650 11100 1750
Entry Wire Line
	11000 1850 11100 1950
Entry Wire Line
	11000 1950 11100 2050
Entry Wire Line
	11000 2050 11100 2150
Entry Wire Line
	11000 2250 11100 2350
Entry Wire Line
	11000 2350 11100 2450
Entry Wire Line
	11000 2450 11100 2550
Entry Wire Line
	11000 2650 11100 2750
Entry Wire Line
	11000 2750 11100 2850
Entry Wire Line
	11000 2850 11100 2950
Entry Wire Line
	11000 3050 11100 3150
Entry Wire Line
	11000 3250 11100 3350
NoConn ~ 9950 3150
NoConn ~ 9450 3050
Wire Bus Line
	11100 1100 11100 6350
Wire Bus Line
	11100 6350 2600 6350
Wire Bus Line
	8400 1100 8400 6350
Wire Wire Line
	9950 1450 10100 1450
Wire Wire Line
	10100 1450 10100 1250
Wire Wire Line
	9950 4550 10100 4550
Wire Wire Line
	10100 4550 10100 5900
Wire Wire Line
	9450 4550 9300 4550
Wire Wire Line
	9300 4350 9300 5900
Wire Wire Line
	9450 4350 9300 4350
Connection ~ 9300 4550
Wire Wire Line
	9450 4950 9300 4950
Connection ~ 9300 4950
Wire Wire Line
	9950 4950 10100 4950
Connection ~ 10100 4950
Wire Wire Line
	9950 1750 10100 1750
Wire Wire Line
	10100 1750 10100 3450
Wire Wire Line
	9450 1750 9300 1750
Wire Wire Line
	9300 1750 9300 3450
Wire Wire Line
	9950 2150 10100 2150
Connection ~ 10100 2150
Wire Wire Line
	9450 2150 9300 2150
Connection ~ 9300 2150
Wire Wire Line
	9950 2550 10100 2550
Connection ~ 10100 2550
Wire Wire Line
	9450 2550 9300 2550
Connection ~ 9300 2550
Wire Wire Line
	9950 2950 10100 2950
Connection ~ 10100 2950
Wire Wire Line
	9450 2950 9300 2950
Connection ~ 9300 2950
Wire Wire Line
	9950 3350 10100 3350
Connection ~ 10100 3350
Wire Wire Line
	9450 3350 9300 3350
Connection ~ 9300 3350
Wire Wire Line
	9950 1550 11000 1550
Wire Wire Line
	9950 1650 11000 1650
Wire Wire Line
	9950 1850 11000 1850
Wire Wire Line
	9950 1950 11000 1950
Wire Wire Line
	9950 2050 11000 2050
Wire Wire Line
	9950 2250 11000 2250
Wire Wire Line
	9950 2350 11000 2350
Wire Wire Line
	9950 2450 11000 2450
Wire Wire Line
	9950 2650 11000 2650
Wire Wire Line
	9950 2750 11000 2750
Wire Wire Line
	9950 2850 11000 2850
Wire Wire Line
	9950 3050 11000 3050
Wire Wire Line
	9950 3250 11000 3250
Wire Wire Line
	9450 1650 8500 1650
Wire Wire Line
	9450 1850 8500 1850
Wire Wire Line
	9450 1950 8500 1950
Wire Wire Line
	9450 2050 8500 2050
Wire Wire Line
	9450 2250 8500 2250
Wire Wire Line
	9450 2350 8500 2350
Wire Wire Line
	9450 2450 8500 2450
Wire Wire Line
	9450 2750 8500 2750
Wire Wire Line
	9450 2850 8500 2850
Wire Wire Line
	9450 3150 8500 3150
Wire Wire Line
	9450 3250 8500 3250
Entry Wire Line
	8400 1750 8500 1650
Entry Wire Line
	8400 1950 8500 1850
Entry Wire Line
	8400 2050 8500 1950
Entry Wire Line
	8400 2150 8500 2050
Entry Wire Line
	8400 2350 8500 2250
Entry Wire Line
	8400 2450 8500 2350
Entry Wire Line
	8400 2550 8500 2450
Entry Wire Line
	8400 2850 8500 2750
Entry Wire Line
	8400 2950 8500 2850
Entry Wire Line
	8400 3250 8500 3150
Entry Wire Line
	8400 3350 8500 3250
Wire Wire Line
	9950 4650 11000 4650
Wire Wire Line
	9950 4750 11000 4750
Wire Wire Line
	9950 4850 11000 4850
Wire Wire Line
	9950 5050 11000 5050
Wire Wire Line
	9450 4650 8500 4650
Wire Wire Line
	9450 4750 8500 4750
Wire Wire Line
	9450 4850 8500 4850
Wire Wire Line
	9450 5050 8500 5050
Wire Wire Line
	9450 5150 8500 5150
Wire Wire Line
	9450 5250 8500 5250
Entry Wire Line
	8400 4750 8500 4650
Entry Wire Line
	8400 4850 8500 4750
Entry Wire Line
	8400 4950 8500 4850
Entry Wire Line
	8400 5150 8500 5050
Entry Wire Line
	8400 5250 8500 5150
Entry Wire Line
	8400 5350 8500 5250
Entry Wire Line
	11000 4650 11100 4750
Entry Wire Line
	11000 4750 11100 4850
Entry Wire Line
	11000 4850 11100 4950
Entry Wire Line
	11000 5050 11100 5150
Text Notes 10150 1450 0    60   ~ 0
VCCIO1
Text Notes 10150 1550 0    60   ~ 0
R15
Text Notes 10150 1650 0    60   ~ 0
P15
Text Notes 10150 1850 0    60   ~ 0
M15
Text Notes 10150 1950 0    60   ~ 0
L16
Text Notes 10150 2050 0    60   ~ 0
K16
Text Notes 10150 2250 0    60   ~ 0
J14
Text Notes 10150 2350 0    60   ~ 0
F14
Text Notes 10150 2450 0    60   ~ 0
H14
Text Notes 10150 2650 0    60   ~ 0
G15
Text Notes 10150 2750 0    60   ~ 0
F15
Text Notes 10150 2850 0    60   ~ 0
E14
Text Notes 10150 3050 0    60   ~ 0
D15
Text Notes 10150 3250 0    60   ~ 0
B16
Text Notes 9050 1650 0    60   ~ 0
P16
Text Notes 9050 1850 0    60   ~ 0
N16
Text Notes 9050 1950 0    60   ~ 0
M16
Text Notes 9050 2050 0    60   ~ 0
K15
Text Notes 9050 2250 0    60   ~ 0
K14
Text Notes 9050 2350 0    60   ~ 0
G14
Text Notes 9050 2450 0    60   ~ 0
J15
Text Notes 9050 2750 0    60   ~ 0
G16
Text Notes 9050 2850 0    60   ~ 0
F16
Text Notes 9050 3150 0    60   ~ 0
D16
Text Notes 9050 3250 0    60   ~ 0
C16
Text Notes 10150 4650 0    60   ~ 0
B9
Text Notes 10150 4750 0    60   ~ 0
A7
Text Notes 10150 4850 0    60   ~ 0
C7
Text Notes 10150 5050 0    60   ~ 0
C6
Text Notes 9050 4350 0    60   ~ 0
A11
Text Notes 9050 4650 0    60   ~ 0
A9
Text Notes 9050 4750 0    60   ~ 0
B8
Text Notes 9050 4850 0    60   ~ 0
B7
Text Notes 9050 5050 0    60   ~ 0
A6
Text Notes 9050 5150 0    60   ~ 0
B6
Text Notes 9050 5250 0    60   ~ 0
A5
Text Label 10500 1550 0    60   ~ 0
adr0
Text Label 8550 1650 0    60   ~ 0
adr1
Text Label 10500 1650 0    60   ~ 0
adr2
Text Label 8550 1850 0    60   ~ 0
adr3
Text Label 10500 1850 0    60   ~ 0
adr4
Text Label 8550 1950 0    60   ~ 0
adr5
Text Label 10500 1950 0    60   ~ 0
adr6
Text Label 8550 2050 0    60   ~ 0
adr7
Text Label 10500 2050 0    60   ~ 0
adr8
Text Label 8550 2250 0    60   ~ 0
adr9
Text Label 10500 2250 0    60   ~ 0
adr10
Text Label 8550 2350 0    60   ~ 0
adr11
Text Label 10500 2350 0    60   ~ 0
adr12
Text Label 8550 2450 0    60   ~ 0
adr13
Text Label 10500 2450 0    60   ~ 0
adr14
NoConn ~ 9450 2650
Text Label 10500 2650 0    60   ~ 0
adr15
Text Label 8550 2750 0    60   ~ 0
adr16
Text Label 10500 2750 0    60   ~ 0
adr17
Text Label 8550 2850 0    60   ~ 0
adr18
Text Label 10500 2850 0    60   ~ 0
adr19
Text Notes 9050 3050 0    60   ~ 0
E16
Text Notes 8550 3050 0    60   ~ 0
adr20
Text Label 8550 4650 0    60   ~ 0
data0
Text Label 10500 4650 0    60   ~ 0
data1
Text Label 8550 4750 0    60   ~ 0
data2
Text Label 10500 4750 0    60   ~ 0
data3
Text Label 8550 4850 0    60   ~ 0
data4
Text Label 10500 4850 0    60   ~ 0
data5
Text Label 8550 5050 0    60   ~ 0
data6
Text Label 10500 5050 0    60   ~ 0
data7
Text Label 8550 5150 0    60   ~ 0
~read
Text Label 8550 5250 0    60   ~ 0
~write
Text Label 8550 3150 0    60   ~ 0
~cs_ram
Text Label 8550 3250 0    60   ~ 0
~cs_cram
Text Label 10500 3250 0    60   ~ 0
~cs_crom
Text Label 10500 3050 0    60   ~ 0
~reset
Text Notes 10150 3150 0    60   ~ 0
D14
Text Notes 10500 3150 0    60   ~ 0
~cs_cart
Text Notes 8550 4350 0    60   ~ 0
~emu_mbc
$Comp
L AS6C62256 U2
U 1 1 5AC432DC
P 6900 2200
F 0 "U2" H 6700 3200 50  0000 C CNN
F 1 "AS6C62256" H 6900 1100 50  0000 C CNN
F 2 "" H 6900 2200 50  0001 C CNN
F 3 "" H 6900 2200 50  0001 C CNN
	1    6900 2200
	1    0    0    -1  
$EndComp
$Comp
L AS6C62256 U1
U 1 1 5AC43343
P 4100 2200
F 0 "U1" H 3900 3200 50  0000 C CNN
F 1 "AS6C62256" H 4100 1100 50  0000 C CNN
F 2 "" H 4100 2200 50  0001 C CNN
F 3 "" H 4100 2200 50  0001 C CNN
	1    4100 2200
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U3
U 1 1 5AC43493
P 4100 4700
F 0 "U3" H 3900 5700 50  0000 C CNN
F 1 "AS6C4008" H 4100 3300 50  0000 C CNN
F 2 "" H 4100 4700 50  0001 C CNN
F 3 "" H 4100 4700 50  0001 C CNN
	1    4100 4700
	1    0    0    -1  
$EndComp
$Comp
L AS6C4008 U4
U 1 1 5AC434EE
P 6900 4700
F 0 "U4" H 6700 5700 50  0000 C CNN
F 1 "AS6C4008" H 6900 3300 50  0000 C CNN
F 2 "" H 6900 4700 50  0001 C CNN
F 3 "" H 6900 4700 50  0001 C CNN
	1    6900 4700
	1    0    0    -1  
$EndComp
Wire Bus Line
	5500 6350 5500 1100
Wire Bus Line
	2600 1100 2600 6800
$Comp
L CONN_02X03 J3
U 1 1 5AC44152
P 1550 2300
F 0 "J3" H 1550 2500 50  0000 C CNN
F 1 "CONN_02X03" H 1550 2100 50  0000 C CNN
F 2 "" H 1550 1100 50  0001 C CNN
F 3 "" H 1550 1100 50  0001 C CNN
	1    1550 2300
	1    0    0    -1  
$EndComp
$Comp
L CONN_02X03 J4
U 1 1 5AC44263
P 1550 2900
F 0 "J4" H 1550 3100 50  0000 C CNN
F 1 "CONN_02X03" H 1550 2700 50  0000 C CNN
F 2 "" H 1550 1700 50  0001 C CNN
F 3 "" H 1550 1700 50  0001 C CNN
	1    1550 2900
	1    0    0    -1  
$EndComp
Wire Wire Line
	2050 3200 1100 3200
Wire Wire Line
	1100 3200 1100 2900
Wire Wire Line
	1100 2900 1300 2900
Wire Wire Line
	2050 2300 1800 2300
NoConn ~ 1800 3000
NoConn ~ 1800 2800
NoConn ~ 1300 2400
NoConn ~ 1300 2200
$Comp
L GND #PWR?
U 1 1 5AC448C0
P 1550 3400
F 0 "#PWR?" H 1550 3150 50  0001 C CNN
F 1 "GND" H 1550 3250 50  0000 C CNN
F 2 "" H 1550 3400 50  0001 C CNN
F 3 "" H 1550 3400 50  0001 C CNN
	1    1550 3400
	1    0    0    -1  
$EndComp
$Comp
L VCC #PWR?
U 1 1 5AC448EA
P 1550 1900
F 0 "#PWR?" H 1550 1750 50  0001 C CNN
F 1 "VCC" H 1550 2050 50  0000 C CNN
F 2 "" H 1550 1900 50  0001 C CNN
F 3 "" H 1550 1900 50  0001 C CNN
	1    1550 1900
	1    0    0    -1  
$EndComp
Wire Wire Line
	1300 3000 1200 3000
Wire Wire Line
	1200 3000 1200 3300
Wire Wire Line
	1200 3300 1950 3300
Wire Wire Line
	1550 3300 1550 3400
Wire Wire Line
	1800 2400 1950 2400
Wire Wire Line
	1950 2400 1950 3300
Connection ~ 1550 3300
Wire Wire Line
	1800 2200 1950 2200
Wire Wire Line
	1950 2200 1950 1900
Wire Wire Line
	1950 1900 1200 1900
Wire Wire Line
	1300 2800 1200 2800
Wire Wire Line
	1200 2800 1200 1900
Connection ~ 1550 1900
Wire Wire Line
	1800 2900 2500 2900
Wire Wire Line
	1300 2300 1100 2300
Wire Wire Line
	1100 2300 1100 2000
Wire Wire Line
	1100 2000 2500 2000
Wire Wire Line
	3400 1300 2700 1300
Wire Wire Line
	3400 1400 2700 1400
Wire Wire Line
	3400 1500 2700 1500
Wire Wire Line
	3400 1600 2700 1600
Wire Wire Line
	3400 1700 2700 1700
Wire Wire Line
	3400 1800 2700 1800
Wire Wire Line
	3400 1900 2700 1900
Wire Wire Line
	3400 2000 2700 2000
Wire Wire Line
	3400 2100 2700 2100
Wire Wire Line
	3400 2200 2700 2200
Wire Wire Line
	3400 2300 2700 2300
Wire Wire Line
	3400 2400 2700 2400
Wire Wire Line
	3400 2500 2700 2500
Wire Wire Line
	3400 3000 2700 3000
Wire Wire Line
	3400 3100 2700 3100
Wire Wire Line
	3400 3200 2700 3200
Wire Wire Line
	4800 1300 5400 1300
Wire Wire Line
	4800 1400 5400 1400
Wire Wire Line
	4800 1500 5400 1500
Wire Wire Line
	4800 1600 5400 1600
Wire Wire Line
	4800 1700 5400 1700
Wire Wire Line
	4800 1800 5400 1800
Wire Wire Line
	4800 1900 5400 1900
Wire Wire Line
	4800 2000 5400 2000
Wire Wire Line
	3400 3800 2700 3800
Wire Wire Line
	3400 3900 2700 3900
Wire Wire Line
	3400 4000 2700 4000
Wire Wire Line
	3400 4100 2700 4100
Wire Wire Line
	3400 4200 2700 4200
Wire Wire Line
	3400 4300 2700 4300
Wire Wire Line
	3400 4400 2700 4400
Wire Wire Line
	3400 4500 2700 4500
Wire Wire Line
	3400 4600 2700 4600
Wire Wire Line
	3400 4700 2700 4700
Wire Wire Line
	3400 4800 2700 4800
Wire Wire Line
	3400 4900 2700 4900
Wire Wire Line
	3400 5000 2700 5000
Wire Wire Line
	3400 5100 2700 5100
Wire Wire Line
	3400 5200 2700 5200
Wire Wire Line
	3400 5300 2700 5300
Wire Wire Line
	3400 5400 2700 5400
Wire Wire Line
	3400 5500 2700 5500
Wire Wire Line
	3400 5600 2700 5600
Wire Wire Line
	3400 5900 2700 5900
Wire Wire Line
	3400 6000 2700 6000
Wire Wire Line
	4800 3800 5400 3800
Wire Wire Line
	4800 3900 5400 3900
Wire Wire Line
	4800 4000 5400 4000
Wire Wire Line
	4800 4200 5400 4200
Wire Wire Line
	4800 4300 5400 4300
Wire Wire Line
	4800 4400 5400 4400
Wire Wire Line
	4800 4500 5400 4500
Wire Wire Line
	4800 4100 5400 4100
Wire Wire Line
	6200 1300 5600 1300
Wire Wire Line
	6200 1400 5600 1400
Wire Wire Line
	6200 1500 5600 1500
Wire Wire Line
	6200 1600 5600 1600
Wire Wire Line
	6200 1700 5600 1700
Wire Wire Line
	6200 1800 5600 1800
Wire Wire Line
	6200 1900 5600 1900
Wire Wire Line
	6200 2000 5600 2000
Wire Wire Line
	6200 2100 5600 2100
Wire Wire Line
	6200 2200 5600 2200
Wire Wire Line
	6200 2300 5600 2300
Wire Wire Line
	6200 2400 5600 2400
Wire Wire Line
	6200 2500 5600 2500
Wire Wire Line
	6200 2600 5600 2600
Wire Wire Line
	6200 2700 5600 2700
Wire Wire Line
	6200 3000 5600 3000
Wire Wire Line
	6200 3100 5600 3100
Wire Wire Line
	6200 3200 5600 3200
Wire Wire Line
	7600 1300 8300 1300
Wire Wire Line
	7600 1400 8300 1400
Wire Wire Line
	7600 1500 8300 1500
Wire Wire Line
	7600 1600 8300 1600
Wire Wire Line
	7600 1700 8300 1700
Wire Wire Line
	7600 1800 8300 1800
Wire Wire Line
	7600 1900 8300 1900
Wire Wire Line
	7600 2000 8300 2000
Wire Wire Line
	6200 3800 5600 3800
Wire Wire Line
	6200 3900 5600 3900
Wire Wire Line
	6200 4000 5600 4000
Wire Wire Line
	6200 4100 5600 4100
Wire Wire Line
	6200 4200 5600 4200
Wire Wire Line
	6200 4300 5600 4300
Wire Wire Line
	6200 4400 5600 4400
Wire Wire Line
	6200 4500 5600 4500
Wire Wire Line
	6200 4600 5600 4600
Wire Wire Line
	6200 4700 5600 4700
Wire Wire Line
	6200 4800 5600 4800
Wire Wire Line
	6200 4900 5600 4900
Wire Wire Line
	6200 5000 5600 5000
Wire Wire Line
	6200 5100 5600 5100
Wire Wire Line
	6200 5200 5600 5200
Wire Wire Line
	6200 5300 5600 5300
Wire Wire Line
	6200 5400 5600 5400
Wire Wire Line
	6200 5500 5600 5500
Wire Wire Line
	6200 5600 5600 5600
Wire Wire Line
	6200 5900 5600 5900
Wire Wire Line
	6200 6000 5600 6000
Wire Wire Line
	7600 3800 8300 3800
Wire Wire Line
	7600 3900 8300 3900
Wire Wire Line
	7600 4000 8300 4000
Wire Wire Line
	7600 4100 8300 4100
Wire Wire Line
	7600 4200 8300 4200
Wire Wire Line
	7600 4300 8300 4300
Wire Wire Line
	7600 4400 8300 4400
Wire Wire Line
	7600 4500 8300 4500
Entry Wire Line
	8300 1300 8400 1400
Entry Wire Line
	8300 1400 8400 1500
Entry Wire Line
	8300 1500 8400 1600
Entry Wire Line
	8300 1600 8400 1700
Entry Wire Line
	8300 1700 8400 1800
Entry Wire Line
	8300 1800 8400 1900
Entry Wire Line
	8300 1900 8400 2000
Entry Wire Line
	8300 2000 8400 2100
Entry Wire Line
	8300 3800 8400 3900
Entry Wire Line
	8300 3900 8400 4000
Entry Wire Line
	8300 4000 8400 4100
Entry Wire Line
	8300 4100 8400 4200
Entry Wire Line
	8300 4200 8400 4300
Entry Wire Line
	8300 4300 8400 4400
Entry Wire Line
	8300 4400 8400 4500
Entry Wire Line
	8300 4500 8400 4600
Entry Wire Line
	5400 1300 5500 1400
Entry Wire Line
	5400 1400 5500 1500
Entry Wire Line
	5400 1500 5500 1600
Entry Wire Line
	5400 1600 5500 1700
Entry Wire Line
	5400 1700 5500 1800
Entry Wire Line
	5400 1800 5500 1900
Entry Wire Line
	5400 1900 5500 2000
Entry Wire Line
	5400 2000 5500 2100
Entry Wire Line
	5400 3800 5500 3900
Entry Wire Line
	5400 3900 5500 4000
Entry Wire Line
	5400 4000 5500 4100
Entry Wire Line
	5400 4100 5500 4200
Entry Wire Line
	5400 4200 5500 4300
Entry Wire Line
	5400 4300 5500 4400
Entry Wire Line
	5400 4400 5500 4500
Entry Wire Line
	5400 4500 5500 4600
Entry Wire Line
	2500 2000 2600 2100
Entry Wire Line
	2500 2900 2600 3000
Entry Wire Line
	2600 1400 2700 1300
Entry Wire Line
	2600 1500 2700 1400
Entry Wire Line
	2600 1600 2700 1500
Entry Wire Line
	2600 1700 2700 1600
Entry Wire Line
	2600 1800 2700 1700
Entry Wire Line
	2600 1900 2700 1800
Entry Wire Line
	2600 2000 2700 1900
Entry Wire Line
	2600 2100 2700 2000
Entry Wire Line
	2600 2200 2700 2100
Entry Wire Line
	2600 2300 2700 2200
Entry Wire Line
	2600 2400 2700 2300
Entry Wire Line
	2600 2500 2700 2400
Entry Wire Line
	2600 2600 2700 2500
Wire Wire Line
	2050 2300 2050 2700
Wire Wire Line
	2050 2700 2950 2700
Wire Wire Line
	2950 2700 2950 2600
Wire Wire Line
	2950 2600 3400 2600
Wire Wire Line
	2050 3200 2050 2800
Wire Wire Line
	2050 2800 3100 2800
Wire Wire Line
	3100 2800 3100 2700
Wire Wire Line
	3100 2700 3400 2700
Entry Wire Line
	2600 3100 2700 3000
Entry Wire Line
	2600 3200 2700 3100
Entry Wire Line
	2600 3300 2700 3200
Entry Wire Line
	2600 3900 2700 3800
Entry Wire Line
	2600 4000 2700 3900
Entry Wire Line
	2600 4100 2700 4000
Entry Wire Line
	2600 4200 2700 4100
Entry Wire Line
	2600 4300 2700 4200
Entry Wire Line
	2600 4400 2700 4300
Entry Wire Line
	2600 4500 2700 4400
Entry Wire Line
	2600 4600 2700 4500
Entry Wire Line
	2600 4700 2700 4600
Entry Wire Line
	2600 4800 2700 4700
Entry Wire Line
	2600 4900 2700 4800
Entry Wire Line
	2600 5000 2700 4900
Entry Wire Line
	2600 5100 2700 5000
Entry Wire Line
	2600 5200 2700 5100
Entry Wire Line
	2600 5300 2700 5200
Entry Wire Line
	2600 5400 2700 5300
Entry Wire Line
	2600 5500 2700 5400
Entry Wire Line
	2600 5600 2700 5500
Entry Wire Line
	2600 5700 2700 5600
Entry Wire Line
	2600 6000 2700 5900
Entry Wire Line
	2600 6100 2700 6000
Entry Wire Line
	5500 1400 5600 1300
Entry Wire Line
	5500 1500 5600 1400
Entry Wire Line
	5500 1600 5600 1500
Entry Wire Line
	5500 1700 5600 1600
Entry Wire Line
	5500 1800 5600 1700
Entry Wire Line
	5500 1900 5600 1800
Entry Wire Line
	5500 2000 5600 1900
Entry Wire Line
	5500 2100 5600 2000
Entry Wire Line
	5500 2200 5600 2100
Entry Wire Line
	5500 2300 5600 2200
Entry Wire Line
	5500 2400 5600 2300
Entry Wire Line
	5500 2500 5600 2400
Entry Wire Line
	5500 2600 5600 2500
Entry Wire Line
	5500 2700 5600 2600
Entry Wire Line
	5500 2800 5600 2700
Entry Wire Line
	5500 3100 5600 3000
Entry Wire Line
	5500 3200 5600 3100
Entry Wire Line
	5500 3300 5600 3200
Entry Wire Line
	5500 3900 5600 3800
Entry Wire Line
	5500 4000 5600 3900
Entry Wire Line
	5500 4100 5600 4000
Entry Wire Line
	5500 4200 5600 4100
Entry Wire Line
	5500 4300 5600 4200
Entry Wire Line
	5500 4400 5600 4300
Entry Wire Line
	5500 4500 5600 4400
Entry Wire Line
	5500 4600 5600 4500
Entry Wire Line
	5500 4700 5600 4600
Entry Wire Line
	5500 4800 5600 4700
Entry Wire Line
	5500 4900 5600 4800
Entry Wire Line
	5500 5000 5600 4900
Entry Wire Line
	5500 5100 5600 5000
Entry Wire Line
	5500 5200 5600 5100
Entry Wire Line
	5500 5300 5600 5200
Entry Wire Line
	5500 5400 5600 5300
Entry Wire Line
	5500 5500 5600 5400
Entry Wire Line
	5500 5600 5600 5500
Entry Wire Line
	5500 5700 5600 5600
Entry Wire Line
	5500 6000 5600 5900
Entry Wire Line
	5500 6100 5600 6000
Text Label 7800 1300 0    60   ~ 0
data0
Text Label 7800 1400 0    60   ~ 0
data1
Text Label 7800 1500 0    60   ~ 0
data2
Text Label 7800 1600 0    60   ~ 0
data3
Text Label 7800 1700 0    60   ~ 0
data4
Text Label 7800 1800 0    60   ~ 0
data5
Text Label 7800 1900 0    60   ~ 0
data6
Text Label 7800 2000 0    60   ~ 0
data7
Text Label 7800 3800 0    60   ~ 0
data0
Text Label 7800 3900 0    60   ~ 0
data1
Text Label 7800 4000 0    60   ~ 0
data2
Text Label 7800 4100 0    60   ~ 0
data3
Text Label 7800 4200 0    60   ~ 0
data4
Text Label 7800 4300 0    60   ~ 0
data5
Text Label 7800 4400 0    60   ~ 0
data6
Text Label 7800 4500 0    60   ~ 0
data7
Text Label 5000 1300 0    60   ~ 0
data0
Text Label 5000 1400 0    60   ~ 0
data1
Text Label 5000 1500 0    60   ~ 0
data2
Text Label 5000 1600 0    60   ~ 0
data3
Text Label 5000 1700 0    60   ~ 0
data4
Text Label 5000 1800 0    60   ~ 0
data5
Text Label 5000 1900 0    60   ~ 0
data6
Text Label 5000 2000 0    60   ~ 0
data7
Text Label 5000 3800 0    60   ~ 0
data0
Text Label 5000 3900 0    60   ~ 0
data1
Text Label 5000 4000 0    60   ~ 0
data2
Text Label 5000 4100 0    60   ~ 0
data3
Text Label 5000 4200 0    60   ~ 0
data4
Text Label 5000 4300 0    60   ~ 0
data5
Text Label 5000 4400 0    60   ~ 0
data6
Text Label 5000 4500 0    60   ~ 0
data7
Text Label 5700 1300 0    60   ~ 0
adr0
Text Label 5700 1400 0    60   ~ 0
adr1
Text Label 5700 1500 0    60   ~ 0
adr2
Text Label 5700 1600 0    60   ~ 0
adr3
Text Label 5700 1700 0    60   ~ 0
adr4
Text Label 5700 1800 0    60   ~ 0
adr5
Text Label 5700 1900 0    60   ~ 0
adr6
Text Label 5700 2000 0    60   ~ 0
adr7
Text Label 5700 2100 0    60   ~ 0
adr8
Text Label 5700 2200 0    60   ~ 0
adr9
Text Label 5700 2300 0    60   ~ 0
adr10
Text Label 5700 2400 0    60   ~ 0
adr11
Text Label 5700 2500 0    60   ~ 0
adr12
Text Label 5700 2600 0    60   ~ 0
adr13
Text Label 5700 2700 0    60   ~ 0
adr14
Text Label 2800 1300 0    60   ~ 0
adr0
Text Label 2800 1400 0    60   ~ 0
adr1
Text Label 2800 1500 0    60   ~ 0
adr2
Text Label 2800 1600 0    60   ~ 0
adr3
Text Label 2800 1700 0    60   ~ 0
adr4
Text Label 2800 1800 0    60   ~ 0
adr5
Text Label 2800 1900 0    60   ~ 0
adr6
Text Label 2800 2000 0    60   ~ 0
adr7
Text Label 2800 2100 0    60   ~ 0
adr8
Text Label 2800 2200 0    60   ~ 0
adr9
Text Label 2800 2300 0    60   ~ 0
adr10
Text Label 2800 2400 0    60   ~ 0
adr11
Text Label 2800 2500 0    60   ~ 0
adr12
Text Label 2150 2000 0    60   ~ 0
adr13
Text Label 2150 2900 0    60   ~ 0
adr14
Text Label 2800 3000 0    60   ~ 0
~cs_ram
Text Label 2800 3100 0    60   ~ 0
~read
Text Label 2800 3200 0    60   ~ 0
~write
Text Label 5700 3000 0    60   ~ 0
~cs_cram
Text Label 5700 3100 0    60   ~ 0
~read
Text Label 5700 3200 0    60   ~ 0
~write
Text Label 5700 3800 0    60   ~ 0
adr0
Text Label 5700 3900 0    60   ~ 0
adr1
Text Label 5700 4000 0    60   ~ 0
adr2
Text Label 5700 4100 0    60   ~ 0
adr3
Text Label 5700 4200 0    60   ~ 0
adr4
Text Label 5700 4300 0    60   ~ 0
adr5
Text Label 5700 4400 0    60   ~ 0
adr6
Text Label 5700 4500 0    60   ~ 0
adr7
Text Label 5700 4600 0    60   ~ 0
adr8
Text Label 5700 4700 0    60   ~ 0
adr9
Text Label 5700 4800 0    60   ~ 0
adr10
Text Label 5700 4900 0    60   ~ 0
adr11
Text Label 5700 5000 0    60   ~ 0
adr12
Text Label 5700 5100 0    60   ~ 0
adr13
Text Label 5700 5200 0    60   ~ 0
adr14
Text Label 5700 5300 0    60   ~ 0
adr15
Text Label 5700 5400 0    60   ~ 0
adr16
Text Label 5700 5500 0    60   ~ 0
adr17
Text Label 5700 5600 0    60   ~ 0
adr18
Text Label 5700 5900 0    60   ~ 0
~read
Text Label 5700 6000 0    60   ~ 0
~write
Text Label 2800 3800 0    60   ~ 0
adr0
Text Label 2800 3900 0    60   ~ 0
adr1
Text Label 2800 4000 0    60   ~ 0
adr2
Text Label 2800 4100 0    60   ~ 0
adr3
Text Label 2800 4200 0    60   ~ 0
adr4
Text Label 2800 4300 0    60   ~ 0
adr5
Text Label 2800 4400 0    60   ~ 0
adr6
Text Label 2800 4500 0    60   ~ 0
adr7
Text Label 2800 4600 0    60   ~ 0
adr8
Text Label 2800 4700 0    60   ~ 0
adr9
Text Label 2800 4800 0    60   ~ 0
adr10
Text Label 2800 4900 0    60   ~ 0
adr11
Text Label 2800 5000 0    60   ~ 0
adr12
Text Label 2800 5100 0    60   ~ 0
adr13
Text Label 2800 5200 0    60   ~ 0
adr14
Text Label 2800 5300 0    60   ~ 0
adr15
Text Label 2800 5400 0    60   ~ 0
adr16
Text Label 2800 5500 0    60   ~ 0
adr17
Text Label 2800 5600 0    60   ~ 0
adr18
Text Label 2800 5900 0    60   ~ 0
~read
Text Label 2800 6000 0    60   ~ 0
~write
Wire Wire Line
	950  5500 750  5500
Wire Wire Line
	750  5200 750  6000
Wire Wire Line
	750  6000 950  6000
Wire Wire Line
	750  5200 2500 5200
Connection ~ 750  5500
Entry Wire Line
	2500 5200 2600 5300
Text Label 2050 5200 0    60   ~ 0
~cs_crom
Wire Wire Line
	2500 4500 1050 4500
Wire Wire Line
	1050 4500 1050 4800
Wire Wire Line
	1050 4800 600  4800
Wire Wire Line
	600  4800 600  5700
Wire Wire Line
	600  5700 950  5700
Connection ~ 1050 4800
Entry Wire Line
	2500 4500 2600 4600
Text Label 2050 4500 0    60   ~ 0
adr19
Wire Wire Line
	1950 4800 1950 5100
Wire Wire Line
	1950 5100 850  5100
Wire Wire Line
	850  5100 850  6200
Wire Wire Line
	850  6200 950  6200
Wire Wire Line
	2150 5600 2300 5600
Wire Wire Line
	2300 5600 2300 5800
Wire Wire Line
	2300 5800 3400 5800
Wire Wire Line
	2150 6100 2400 6100
Wire Wire Line
	2400 6100 2400 6200
Wire Wire Line
	2400 6200 5050 6200
Wire Wire Line
	5050 6200 5050 5800
Wire Wire Line
	5050 5800 6200 5800
$Comp
L CONN_01X03 J5
U 1 1 5AC4CC32
P 1600 7000
F 0 "J5" H 1600 7200 50  0000 C CNN
F 1 "CONN_01X03" V 1700 7000 50  0000 C CNN
F 2 "" H 1600 7000 50  0001 C CNN
F 3 "" H 1600 7000 50  0001 C CNN
	1    1600 7000
	1    0    0    -1  
$EndComp
NoConn ~ 1400 7100
$Comp
L GND #PWR?
U 1 1 5AC4D17D
P 1200 7200
F 0 "#PWR?" H 1200 6950 50  0001 C CNN
F 1 "GND" H 1200 7050 50  0000 C CNN
F 2 "" H 1200 7200 50  0001 C CNN
F 3 "" H 1200 7200 50  0001 C CNN
	1    1200 7200
	1    0    0    -1  
$EndComp
Wire Wire Line
	1400 7000 1200 7000
Wire Wire Line
	1200 7000 1200 7200
Wire Wire Line
	1100 6900 1400 6900
Wire Wire Line
	1200 6900 1200 6550
Wire Wire Line
	1200 6550 2500 6550
Entry Wire Line
	2500 6550 2600 6650
Text Label 2050 6550 0    60   ~ 0
~reset
$Comp
L VCC #PWR?
U 1 1 5AC4D98C
P 700 6600
F 0 "#PWR?" H 700 6450 50  0001 C CNN
F 1 "VCC" H 700 6750 50  0000 C CNN
F 2 "" H 700 6600 50  0001 C CNN
F 3 "" H 700 6600 50  0001 C CNN
	1    700  6600
	1    0    0    -1  
$EndComp
$Comp
L R R1
U 1 1 5AC4D9B8
P 950 6900
F 0 "R1" V 1030 6900 50  0000 C CNN
F 1 "1K" V 950 6900 50  0000 C CNN
F 2 "" V 880 6900 50  0001 C CNN
F 3 "" H 950 6900 50  0001 C CNN
	1    950  6900
	0    1    1    0   
$EndComp
Connection ~ 1200 6900
Wire Wire Line
	800  6900 700  6900
Wire Wire Line
	700  6900 700  6600
$Comp
L C C1
U 1 1 5AC4E41F
P 3200 7050
F 0 "C1" H 3225 7150 50  0000 L CNN
F 1 "100n" H 3225 6950 50  0000 L CNN
F 2 "" H 3238 6900 50  0001 C CNN
F 3 "" H 3200 7050 50  0001 C CNN
	1    3200 7050
	1    0    0    -1  
$EndComp
$Comp
L C C2
U 1 1 5AC4E466
P 3600 7050
F 0 "C2" H 3625 7150 50  0000 L CNN
F 1 "100n" H 3625 6950 50  0000 L CNN
F 2 "" H 3638 6900 50  0001 C CNN
F 3 "" H 3600 7050 50  0001 C CNN
	1    3600 7050
	1    0    0    -1  
$EndComp
$Comp
L C C3
U 1 1 5AC4E49B
P 4000 7050
F 0 "C3" H 4025 7150 50  0000 L CNN
F 1 "100n" H 4025 6950 50  0000 L CNN
F 2 "" H 4038 6900 50  0001 C CNN
F 3 "" H 4000 7050 50  0001 C CNN
	1    4000 7050
	1    0    0    -1  
$EndComp
$Comp
L C C4
U 1 1 5AC4E4DE
P 4400 7050
F 0 "C4" H 4425 7150 50  0000 L CNN
F 1 "100n" H 4425 6950 50  0000 L CNN
F 2 "" H 4438 6900 50  0001 C CNN
F 3 "" H 4400 7050 50  0001 C CNN
	1    4400 7050
	1    0    0    -1  
$EndComp
$Comp
L C C5
U 1 1 5AC4E535
P 4800 7050
F 0 "C5" H 4825 7150 50  0000 L CNN
F 1 "100n" H 4825 6950 50  0000 L CNN
F 2 "" H 4838 6900 50  0001 C CNN
F 3 "" H 4800 7050 50  0001 C CNN
	1    4800 7050
	1    0    0    -1  
$EndComp
$Comp
L C C6
U 1 1 5AC4E58A
P 5200 7050
F 0 "C6" H 5225 7150 50  0000 L CNN
F 1 "100n" H 5225 6950 50  0000 L CNN
F 2 "" H 5238 6900 50  0001 C CNN
F 3 "" H 5200 7050 50  0001 C CNN
	1    5200 7050
	1    0    0    -1  
$EndComp
Wire Wire Line
	3200 7200 5200 7200
Connection ~ 4800 7200
Connection ~ 4400 7200
Connection ~ 4000 7200
Connection ~ 3600 7200
Wire Wire Line
	3200 6900 5200 6900
Connection ~ 4800 6900
Connection ~ 4400 6900
Connection ~ 4000 6900
Connection ~ 3600 6900
$Comp
L VCC #PWR?
U 1 1 5AC500DE
P 3200 6900
F 0 "#PWR?" H 3200 6750 50  0001 C CNN
F 1 "VCC" H 3200 7050 50  0000 C CNN
F 2 "" H 3200 6900 50  0001 C CNN
F 3 "" H 3200 6900 50  0001 C CNN
	1    3200 6900
	1    0    0    -1  
$EndComp
Connection ~ 3200 6900
$Comp
L GND #PWR?
U 1 1 5AC5018C
P 3200 7200
F 0 "#PWR?" H 3200 6950 50  0001 C CNN
F 1 "GND" H 3200 7050 50  0000 C CNN
F 2 "" H 3200 7200 50  0001 C CNN
F 3 "" H 3200 7200 50  0001 C CNN
	1    3200 7200
	1    0    0    -1  
$EndComp
Connection ~ 3200 7200
$EndSCHEMATC
