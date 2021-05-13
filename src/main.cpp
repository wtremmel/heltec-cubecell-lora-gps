#include "LoRaWan_APP.h"
#include "Arduino.h"
#include <Wire.h>
#include <ArduinoLog.h>
#include "CubeCell_NeoPixel.h"
#include "innerWdt.h"
#include "HT_SSD1306Wire.h"
#include "GPS_Air530Z.h"


#include "cubegps01.h"




// Power management parameters
#define SHUTDOWN_VOLTAGE 2600 // 2.6V
#define RESTART_VOLTAGE 3000  // 3.0V
#define HIBERNATION_SLEEPTIME 60*1000*5  // 5 minutes
#define CYCLE_MIN  60000  // 1 minute
#define CYCLE_MAX 240000  // 4 minutes
#define VOLTAGE_MAX 3900  // 3.9V
#define VOLTAGE_MIN 3000  // 3.0V

uint16_t lastV = 0;
bool hibernationMode = false;
uint32_t last_cycle = HIBERNATION_SLEEPTIME;


// Global Objects
CubeCell_NeoPixel pixels(1, RGB, NEO_GRB + NEO_KHZ800);
SSD1306Wire  display(0x3c, 500000, SDA, SCL, GEOMETRY_128_64, GPIO10); // addr , freq , SDA, SCL, resolution , rst
Air530ZClass GPS;


bool voltage_found = true;

bool setup_complete = false;
bool pixels_initalized = false;
bool drain_battery = true;

uint16_t userChannelsMask[6]={ 0x00FF,0x0000,0x0000,0x0000,0x0000,0x0000 };
uint8_t nwkSKey[] = { 0x15, 0xb1, 0xd0, 0xef, 0xa4, 0x63, 0xdf, 0xbe, 0x3d, 0x11, 0x18, 0x1e, 0x1e, 0xc7, 0xda,0x85 };
uint8_t appSKey[] = { 0xd7, 0x2c, 0x78, 0x75, 0x8c, 0xdc, 0xca, 0xbf, 0x55, 0xee, 0x4a, 0x77, 0x8d, 0x16, 0xef,0x67 };
uint32_t devAddr;
/*LoraWan region, select in arduino IDE tools*/
LoRaMacRegion_t loraWanRegion = ACTIVE_REGION;

/*LoraWan Class, Class A and Class C are supported*/
DeviceClass_t  loraWanClass = LORAWAN_CLASS;

/*the application data transmission duty cycle.  value in [ms].*/
uint32_t appTxDutyCycle = CYCLE_MIN;
bool variableDutyCycle = true;

/*OTAA or ABP*/
bool overTheAirActivation = LORAWAN_NETMODE;

/*ADR enable*/
bool loraWanAdr = LORAWAN_ADR;

/* set LORAWAN_Net_Reserve ON, the node could save the network info to flash, when node reset not need to join again */
bool keepNet = LORAWAN_NET_RESERVE;

/* Indicates if the node is sending confirmed or unconfirmed messages */
bool isTxConfirmed = LORAWAN_UPLINKMODE;

/* Application port */
uint8_t appPort = 2;

uint8_t ledr = 0, ledg = 0, ledb = 0;
bool ledon = false;

/*!
* Number of trials to transmit the frame, if the LoRaMAC layer did not
* receive an acknowledgment. The MAC performs a datarate adaptation,
* according to the LoRaWAN Specification V1.0.2, chapter 18.4, according
* to the following table:
*
* Transmission nb | Data Rate
* ----------------|-----------
* 1 (first)       | DR
* 2               | DR
* 3               | max(DR-1,0)
* 4               | max(DR-1,0)
* 5               | max(DR-2,0)
* 6               | max(DR-2,0)
* 7               | max(DR-3,0)
* 8               | max(DR-3,0)
*
* Note, that if NbTrials is set to 1 or 2, the MAC will not decrease
* the datarate, in case the LoRaMAC layer did not receive an acknowledgment
*/
uint8_t confirmedNbTrials = 4;


// GPS related stuff
typedef struct sendObject {
  uint32_t timestamp;
  uint32_t gpslong, gpslat, gpsalt;
  uint32_t speed, direction;
  uint16_t voltage;
  uint8_t listlen;
} sendObject_t;

typedef struct list {
  sendObject_t *o;
  bool queued;
  struct list *nxt,*prv;
} list_t;

list_t *firstInList = NULL,
  *lastInList = NULL,
  *deletedList;


// external power functions
void vext_power(bool on) {
  if (on && !hibernationMode) {
    digitalWrite(Vext,LOW);
  } else {
    digitalWrite(Vext,HIGH);
  }
}

void set_led(uint8_t r, uint8_t g, uint8_t b) {
  // switch on power
  vext_power(true);

  Log.verbose(F("set_led(%d,%d,%d)"),r,g,b);
  if (!pixels_initalized){
    pixels.begin();
    pixels_initalized = true;
  }

  if (r == 0 && g == 0 && b == 0) {
    pixels.clear();
    pixels.show();
  } else {
    pixels.setPixelColor(0, pixels.Color(r,g,b));
    pixels.show();
    // delay(10*1000);
  }
}


void set_hibernation(bool on) {
  if (on) {
    if (!hibernationMode) {
    hibernationMode = true;
    Log.notice(F("Hibernation mode now on"));
    set_led(0,0,0);
    vext_power(false);
    appTxDutyCycle = HIBERNATION_SLEEPTIME;
    drain_battery = false;
    variableDutyCycle = false;
    } else {
      Log.verbose(F("Hibernation mode already on, doing nothing"));
    }
  } else {
    if (hibernationMode) {
      hibernationMode = false;
      appTxDutyCycle = HIBERNATION_SLEEPTIME;
      variableDutyCycle = true;
      vext_power(true);
      Log.notice(F("Hibernation mode now off"));
    } else {
      Log.verbose(F("Hibernation mode already off, doing nothing"));
    }
  }
}

//
// Scan for sensors
//
void setup_i2c() {
  byte error, address;
  unsigned int devices=0;

// 0x29 TSL45315 (Light)
// 0x38 VEML6070 (Light)
// 0x39 TSL2561
// 0x40 SI7021
// 0x48 4*AD converter
// 0x4a GY49 or MAX44009 Light Sensor
// 0x50 PCF8583P
// 0x57 ATMEL732
// 0x68 DS3231 Clock
// 0x76 BME280
// 0x77 BME680 (also BMP180)

  Log.verbose("Scanning i2c bus");
  Wire.begin();
  for(address = 1; address < 127; address++ ) {
    Log.verbose(F("Trying 0x%x"),address);
    Wire.beginTransmission(address);
    error = Wire.endTransmission();

    if (error == 0) {
      Log.verbose(F("I2C device found at address 0x%x !"),address);
      devices++;


    }
  }
  Log.verbose(F("i2c bus scanning complete, %d devices"),devices);
}


// Battery voltage
void read_voltage() {
  uint16_t v = getBatteryVoltage();
  lpp.addAnalogInput(5,(float)v / 1000.0);
  Log.verbose(F("Voltage: %d"),v);
  if (!hibernationMode && v <= SHUTDOWN_VOLTAGE) {
    Log.notice(F("Voltage %d < Shutdown voltage (%d), hibernation mode"),v,SHUTDOWN_VOLTAGE);
    set_hibernation(true);
    lastV = v;
  }
  if (hibernationMode && v >= RESTART_VOLTAGE) {
    set_hibernation(false);
  }

  if (hibernationMode) {
    if (v < lastV)
      appTxDutyCycle += HIBERNATION_SLEEPTIME;
    if (v > lastV)
      appTxDutyCycle = HIBERNATION_SLEEPTIME;

    lastV = v;
  }
  else if (variableDutyCycle) {
    // duty cycle depending on voltage
    // max duty cycle = 4 minutes = 240000
    // min duty cycle = 1 minute = 60000
    // min voltage = 3000
    // max voltage = 3900


    // ((t2-t1)/(v2-v1))*(v-v1)+t1
    long int cycle = ((CYCLE_MIN - CYCLE_MAX)/(VOLTAGE_MAX-VOLTAGE_MIN)) * (v - VOLTAGE_MIN) + CYCLE_MAX;
    if (cycle < CYCLE_MIN)
      appTxDutyCycle = CYCLE_MIN;
    else if (cycle > CYCLE_MAX)
      appTxDutyCycle = CYCLE_MAX;
    else
      appTxDutyCycle = abs(cycle);

    Log.verbose(F("Duty cycle: %d s"),int(appTxDutyCycle / 1000));
  }
}

void read_GPS() {
  // reads GPS and stores result if conditions are met
  Log.verbose(F("readGPS start"));
  if (!GPS) {
    Log.verbose(F("Initializing GPS"));
    GPS.begin(9600);
  }
  Log.verbose(F("Reading GPS"));
  unsigned long start = millis();
  do {
    while (GPS.available() > 0) {
      gps.encode(GPS.read());
    }
  } while (millis() - start < 1000 || gps_wait_for_loc);
  if (gps.charsProcessed() < 10) {
    Log.notice(F("No GPS data received"));
    nextGPS = millis() + 1*60*1000; // try again in 1 minute
  } else {
    if (gps.location.isValid() && gps.location.isUpdated()) {
      lastGPS = millis();
      Log.notice(F("GPS data: lat(%F) long(%F) height(%F)"),
        (double)(gps.location.lat()),
        (double)(gps.location.lng()),
        (double)(gps.altitude.meters()));

      whereAmI.gpslong = (uint32_t) (gps.location.lng() * 10000);
      whereAmI.gpslat = (uint32_t) (gps.location.lat() * 10000);
      whereAmI.gpsalt = (uint32_t) (gps.altitude.meters() * 100);
      whereAmI.speed = (uint32_t) (gps.speed.kmph() * 100);
      whereAmI.direction = (uint32_t) (gps.course.deg() * 100);

      Log.verbose(F("GPS movement: speed(%F km/h) deg(%F) "),
        gps.speed.kmph(),
        gps.course.deg());


      struct tm tm;
      tm.tm_sec=gps.time.second();
      tm.tm_min=gps.time.minute();
      tm.tm_hour=gps.time.hour();
      tm.tm_mday=gps.date.day();
      tm.tm_mon=gps.date.month()-1;
      tm.tm_year=gps.date.year()-1900;

      whereAmI.timestamp = (uint32_t) mktime(&tm);
      Log.verbose(F("Unix time %l"),whereAmI.timestamp);
      Log.verbose(F("ctime = %s"),ctime((time_t *) &whereAmI.timestamp));

      whereAmI.voltage = (uint16_t)(getBatteryVoltage() * 100.0);

      // only push if we have changed location
      float gpsdelta = abs(gps.location.lng()-lastlong) +
            abs(gps.location.lat()-lastlat);
      if (gpsdelta > 0.0002 &&
          int(gps.location.lng()) != 0 &&
          int(gps.location.lat()) != 0
          ) {
        pushrtcbuffer(&whereAmI);
        lastlat = gps.location.lat();
        lastlong= gps.location.lng();
        lastVoltage = whereAmI.voltage;
        nopushfor = 0;
      } else {
        Log.verbose(F("GPS delta too small (%F), not pushing"),gpsdelta);
      }

      // calculate next data gathering
      // speed = 0 -> 5 minutes
      // speed < 3 -> 2 minutes
      // speed < 30 -> 1 minute
      // speed < 100 -> 30s
      // speed > 100 -> 10s

      if (whereAmI.speed == 0)
        nextGPS = lastGPS+(60*1000);
      else
        nextGPS = lastGPS+10*1000;
    } else {
      Log.verbose(F("GPS valid: %T GPS update: %T"),
        gps.location.isValid(),
        gps.location.isUpdated());
      nextGPS = millis() + 5*1000;
    }
  }
}


// Sensor routines
void read_sensors() {
  lpp.reset();

  // switch on power
  vext_power(true);
  set_led(ledr,ledg,ledb);

  delay(100);

  if (voltage_found) {
    read_voltage();
  }

  // initialize sensors

  if (!hibernationMode) {
    setup_i2c();


    Wire.end();
  }

  read_gps();
}

void setup_serial() {
  Serial.begin(115200);
#if DEBUG
  while (!Serial);
#endif
}


// Logging helper routines
void printTimestamp(Print* _logOutput) {
  char c[12];
  sprintf(c, "%10lu ", TimerGetCurrentTime());
  _logOutput->print(c);
}

void printNewline(Print* _logOutput) {
  _logOutput->print('\n');
}

void setup_logging() {
  Log.begin(LOG_LEVEL_VERBOSE, &Serial);
  Log.setPrefix(printTimestamp);
  Log.setSuffix(printNewline);
  Log.verbose("Logging has started");
}

void setup_lora() {
  Log.verbose(F("setup_lora: start"));
  deviceState = DEVICE_STATE_INIT;
	LoRaWAN.ifskipjoin();
}

void setup_check_voltage() {
  // Check if voltage is above RESTART_VOLTAGE
  uint16_t v = getBatteryVoltage();
  Log.verbose(F("Voltage: %d"),v);

}

void setup_chipid() {
  uint64_t chipID=getID();
  Log.notice(F("Chip ID = %X%x"),
    (uint32_t)(chipID>>32),(uint32_t)chipID);
}

void setup_display() {
  display.init();
  display.setFont(ArialMT_Plain_10);
}

void setup_gps() {
  GPS.begin(9600);
}

void setup() {
  // Turn on watchdog
  innerWdtEnable(true);

  setup_serial();
  delay(5000);
  setup_logging();
  Log.verbose(F("setup(): Logging started"));
  setup_display();
  setup_chipid();
  setup_check_voltage();

  // Turn on power for devices
  pinMode(Vext,OUTPUT);
  vext_power(true);
  set_led(ledr,ledg,ledb);

  setup_i2c();
  setup_lora();

}

static void prepareTxFrame( ) {
  read_sensors();

  appDataSize = lpp.getSize();
  memcpy(appData,lpp.getBuffer(),appDataSize);
}

// -------------- Command Processing -----------------
void process_system_led_command(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length LED command"));
    return;
  } else {
    Log.verbose(F("Processing LED command"));
  }

  switch (buffer[0]) {
    case 0x00:
      ledr = 0;
      ledg = 0;
      ledb = 0;
      set_led(0,0,0);
      break;
    case 0x01:
      ledr = 255;
      ledg = 255;
      ledb = 255;
      set_led(255,255,255);
      break;
    case 0x02:
      if (len == 4) {
        // do rgb magic
        ledr = buffer[1];
        ledg = buffer[2];
        ledb = buffer[3];
        set_led(ledr,ledg,ledb);
      } else {
        Log.error(F("Missing RGB values for LED. Len = %d"),len);
      }
      break;
    default:
      Log.error(F("Unknown LED command %d"), buffer[0]);
      break;
  }
}

void process_system_power_command(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length power command"));
  } else {
    Log.verbose(F("Processing power command"));
  }

  switch (buffer[0]) {
    case 0x01:
      drain_battery = false;
      Log.verbose(F("Power save to default"));
      break;
    case 0x10:
      set_hibernation(true);
      break;
    case 0x11:
      set_hibernation(false);
      break;
    case 0xff:
      drain_battery = true;
      Log.verbose(F("Drain battery on"));
      break;
    default:
      Log.error(F("Unknown power command %d"),buffer[0]);
      break;
  }
}

void process_system_delay_command(unsigned char len, unsigned char *buffer) {
  if (len != 1) {
    Log.error(F("Len of delay command != 1"));
  } else {
    Log.verbose(F("Processing delay command"));
  }

  if (buffer[0] == 0) {
    variableDutyCycle = true;
    Log.verbose(F("Duty cycle variable"));
  } else {
    variableDutyCycle = false;
    appTxDutyCycle = buffer[0] * 1000 * 5;
    Log.verbose(F("Duty cycle %d seconds"),appTxDutyCycle / 1000);
  }
}

void process_system_command(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length system command"));
    return;
  } else {
    Log.verbose(F("Processing system command"));
  }
  switch (buffer[0]) {
    case 0x01:
      process_system_power_command(len-1,buffer+1);
      break;
    case 0x02:
      process_system_delay_command(len-1,buffer+1);
      break;
    case 0x03:
      process_system_led_command(len-1,buffer+1);
      break;
    case 0xff:
      // Reboots
      Log.notice(F("Executing reboot command"));
      delay(100);
      HW_Reset(0);
    default:
      Log.error(F("Unknown system command %d"),buffer[0]);
      break;
  }
}

void process_sensor_bme280(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length bme280 command"));
    return;
  }

}

void process_sensor_command(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length sensor command"));
    return;
  }
  switch (buffer[0]) {
    case 0x11:
      process_sensor_bme280(len-1,buffer+1);
      break;
    default:
      Log.error(F("Unknown sensor command %d"),buffer[0]);
      break;
  }
}

void process_received_lora(unsigned char len, unsigned char *buffer) {
  if (len == 0)
    return;

  Log.verbose(F("Processing %d bytes of received data"),len);
  switch (buffer[0]) {
    case 0:
      process_system_command(len-1,buffer+1);
      break;
    case 1:
      process_sensor_command(len-1,buffer+1);
      break;
    default:
      Log.error(F("Unknown command %d"),buffer[0]);
      break;
  }
}


void downLinkDataHandle(McpsIndication_t *mcpsIndication)
{
  Log.verbose(F("+REV DATA:%s,RXSIZE %d,PORT %d\r\n"),
    mcpsIndication->RxSlot?"RXWIN2":"RXWIN1",
    mcpsIndication->BufferSize,
    mcpsIndication->Port);
  process_received_lora(mcpsIndication->BufferSize, mcpsIndication->Buffer);
}



void loop() {
  setup_complete = true;
  switch( deviceState )
	{
		case DEVICE_STATE_INIT:
		{
			LoRaWAN.generateDeveuiByChipID();
			printDevParam();
			LoRaWAN.init(loraWanClass,loraWanRegion);
			deviceState = DEVICE_STATE_JOIN;
			break;
		}
		case DEVICE_STATE_JOIN:
		{
			LoRaWAN.join();
			break;
		}
		case DEVICE_STATE_SEND:
		{
			// prepareTxFrame( appPort );
      prepareTxFrame();
			LoRaWAN.send();
			deviceState = DEVICE_STATE_CYCLE;
			break;
		}
		case DEVICE_STATE_CYCLE:
		{
			// Schedule next packet transmission
			txDutyCycleTime = appTxDutyCycle + randr( 0, APP_TX_DUTYCYCLE_RND );
			LoRaWAN.cycle(txDutyCycleTime);
			deviceState = DEVICE_STATE_SLEEP;
			break;
		}
		case DEVICE_STATE_SLEEP:
		{
      // switch off power
      if (!drain_battery)
        vext_power(false);
			LoRaWAN.sleep();
			break;
		}
		default:
		{
			deviceState = DEVICE_STATE_INIT;
			break;
		}
	}

}
