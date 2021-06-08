#include "LoRaWan_APP.h"
#include "Arduino.h"
#include "Wire.h"
#include <ArduinoLog.h>
#include "CubeCell_NeoPixel.h"
#include "innerWdt.h"
#include "HT_SSD1306Wire.h"
#include "GPS_Air530Z.h"
#include <time.h>

#include "cubegps01.h"

// Power management parameters
#define SHUTDOWN_VOLTAGE 2600 // 2.6V
#define RESTART_VOLTAGE 3000  // 3.0V
#define HIBERNATION_SLEEPTIME 60*1000*5  // 5 minutes
#define CYCLE_MIN  20*1000  // 35 second
#define CYCLE_MAX 40*1000  // 5 minutes
#define VOLTAGE_MAX 3900  // 3.9V
#define VOLTAGE_MIN 3000  // 3.0V

//fisrt fix timeout
#define GPS_INIT_TIMEOUT 10000

//sleep time until next GPS update
#define GPS_SLEEPTIME 60*1000

//when gps waked, if in GPS_UPDATE_TIMEOUT, gps not fixed then into low power mode
#define GPS_UPDATE_TIMEOUT 1000

//once fixed, GPS_CONTINUE_TIME later into low power mode
#define GPS_CONTINUE_TIME 5000

uint16_t lastV = 0;
bool hibernationMode = false;
bool sleepOK = false, ackReceived = true, dataPrepared = false;
uint32_t last_cycle = HIBERNATION_SLEEPTIME;


// Global Objects
CubeCell_NeoPixel rgbled(1, RGB, NEO_GRB + NEO_KHZ800);
SSD1306Wire dis(0x3c, 500000, SDA, SCL, GEOMETRY_128_64, GPIO10); // addr , freq , SDA, SCL, resolution , rst
Air530ZClass GPS;

uint32_t nextGPS = 0, nextLORA = 0, loraDelta = 0, lastGPS = 0, loraCount=0;


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
uint8_t displayWhat = 1;

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
uint8_t confirmedNbTrials = 8;


// GPS related stuff
typedef struct sendObject {
  uint32_t timestamp;
  uint32_t gpslong, gpslat, gpsalt;
  uint32_t speed, direction;
  uint16_t voltage;
  uint8_t listlen;
  uint32_t hdop;
} sendObject_t;

typedef struct list {
  sendObject_t *o;
  bool queued;
  struct list *nxt,*prv;
} list_t;

list_t *firstInList = NULL,
  *lastInList = NULL,
  *deletedList;

sendObject_t whereAmI;
float lastlat = 0, lastlong = 0;
uint16_t lastVoltage = 0;
uint8_t nopushfor = 0;

int fracPart(double val, int n) {
  return (int)((val - (int)(val))*pow(10,n));
}

char *fracString(double val, int n) {
  static char s[10];
  char buf[8];
  int i;
  int frac = (int)((val - (int)(val))*pow(10,n));
  i = sprintf(buf,"%%0%dd",n);
  buf[i] = 0;
  i= sprintf(s,buf,frac);
  buf[i] = 0;
  return s;
}

uint8_t queueLength() {
  uint8_t i = 0;
  list_t *t = firstInList;
  while (t != NULL && i < 255) {
    i++;
    t = t->nxt;
  }
  return i;
}

bool pushrtcbuffer(sendObject_t *o) {
  list_t *new_member;


  new_member = (list_t *)malloc(sizeof(list_t));
  if (new_member) {
    new_member->o = (sendObject_t *)malloc(sizeof(sendObject_t));
    if (new_member->o == NULL) {
      free(new_member);
      Log.verbose(F("pushrtcbuffer: out of memory"));
      send_confirmed(false);
      return(false);
    }
  }

  // check if we have generated an object
  if (new_member && new_member->o) {
    memcpy(new_member->o,o,sizeof(sendObject_t));
    new_member->queued = false;

    // add it to the chain at the end
    // special case - chain is empty
    if (lastInList == NULL) {
      lastInList = new_member;
      firstInList= new_member;
      new_member->prv = NULL;
      new_member->nxt = NULL;
    } else {
      new_member->prv = lastInList;
      new_member->nxt = NULL;
      lastInList->nxt = new_member;
      lastInList = new_member;
    }
    Log.verbose(F("pushrtcbuffer: true"));
    return true;
  } else {
    Log.verbose(F("pushrtcbuffer: false"));
    return false;
  }
}

sendObject_t *poprtcbuffer() {
  static sendObject_t t;
  // return last object in list and delete list entry
  if (lastInList == NULL) {
    // nothing to do, list is empty
    Log.verbose(F("poprtcbuffer: NULL"));
    return NULL;
  } else {
    sendObject_t *o;
    list_t *prev;

    o = lastInList->o;
    if (lastInList->prv != NULL) {
      lastInList->prv->nxt = NULL;
    } else {
      firstInList = NULL;
    }
    prev = lastInList->prv;
    free(lastInList);
    lastInList = prev;
    o->listlen = queueLength();
    Log.verbose(F("poprtcbuffer: ok, len = %d"),o->listlen);
    memcpy(&t,o,sizeof(sendObject_t));
    free(o);
    return &t;
  }
}

sendObject_t *poprtcbuffer2() {
  static sendObject_t o;
  // remove last object of list
  if (lastInList == NULL) {
    // nothing to do, list is empty
    return NULL;
  } else {
    // do we have an object to copy?
    if (lastInList->o == NULL) {
      // no - dump the last element and return NULL
      list_t *dumpit;
      dumpit = lastInList;
      lastInList = dumpit->prv;
      if (lastInList == NULL)
        firstInList = NULL;
      else
        lastInList->nxt = NULL;
      free(dumpit);
      return NULL;
    } else {
      memcpy(&o,lastInList->o,sizeof(sendObject_t));
      free(lastInList->o);
      list_t *dumpit;
      dumpit = lastInList;
      lastInList = dumpit->prv;
      if (lastInList == NULL)
        firstInList = NULL;
      else
        lastInList->nxt = NULL;
      free(dumpit);
      return &o;
    }
  }
}

uint32_t rtcbuflen() {
  list_t *o = firstInList;
  uint32_t len = 0;

  while (o) {
    len++;
    o = o->nxt;
  }
  return len;
}

void dumprtcbuffer() {
  #if DEBUG
  int buflen = 0;
  list_t *o;
  o = firstInList;
  while (o && buflen < 10000) {
    buflen++;
    o = o->nxt;
  }

  Log.verbose(F("buflen = %d"),buflen);
  #endif
}


// external power functions
void vext_power(bool on) {
  if (on && !hibernationMode) {
    digitalWrite(Vext,LOW);
  } else {
    // digitalWrite(Vext,HIGH);
  }
}

bool send_confirmed(bool on) {
  Log.verbose(F("uplink mode now %T (was %T)"),on,isTxConfirmed);
  isTxConfirmed = on;
  return isTxConfirmed;
}

void set_led(uint8_t r, uint8_t g, uint8_t b) {
  // switch on power
  vext_power(true);

  Log.verbose(F("set_led(%d,%d,%d)"),r,g,b);
  if (!pixels_initalized){
    rgbled.begin();
    pixels_initalized = true;
  }

  if (r == 0 && g == 0 && b == 0) {
    rgbled.clear();
    rgbled.show();
  } else {
    rgbled.setPixelColor(0, rgbled.Color(r,g,b));
    rgbled.show();
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
      appTxDutyCycle = CYCLE_MIN;
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
    // Log.verbose(F("Trying 0x%x"),address);
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
  // lpp.addAnalogInput(5,(float)v / 1000.0);
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
}

void read_GPS(uint32_t timeout) {
  // reads GPS and stores result if conditions are met
  Log.verbose(F("readGPS start"));

  Log.verbose(F("Reading GPS"));
  unsigned long start = millis();
  do {
    while (GPS.available() > 0) {
      GPS.encode(GPS.read());
    }
  } while (millis() - start < timeout);
  if (GPS.charsProcessed() < 10) {
    Log.notice(F("No GPS data received"));
    nextGPS = millis() + GPS_SLEEPTIME; // try again in 1 minute
  } else {
    if (GPS.location.isValid() && GPS.location.isUpdated() &&
        GPS.location.lat() != 0 && GPS.location.lng() != 0) {
      lastGPS = millis();
      Log.notice(F("GPS data: lat(%F) long(%F) height(%F)"),
        (double)(GPS.location.lat()),
        (double)(GPS.location.lng()),
        (double)(GPS.altitude.meters()));

      whereAmI.gpslong = (uint32_t) (GPS.location.lng() * 10000);
      whereAmI.gpslat = (uint32_t) (GPS.location.lat() * 10000);
      whereAmI.gpsalt = (uint32_t) (GPS.altitude.meters() * 100);
      whereAmI.speed = (uint32_t) (GPS.speed.kmph() * 100);
      whereAmI.direction = (uint32_t) (GPS.course.deg() * 100);
      whereAmI.voltage = getBatteryVoltage();
      whereAmI.hdop = (uint32_t) (GPS.hdop.hdop() * 100);

      Log.verbose(F("GPS movement: speed(%F km/h) deg(%F) "),
        GPS.speed.kmph(),
        GPS.course.deg());


      struct tm tm;
      tm.tm_sec=GPS.time.second();
      tm.tm_min=GPS.time.minute();
      tm.tm_hour=GPS.time.hour();
      tm.tm_mday=GPS.date.day();
      tm.tm_mon=GPS.date.month()-1;
      tm.tm_year=GPS.date.year()-1900;

      whereAmI.timestamp = (uint32_t) mktime(&tm);
      Log.verbose(F("Unix time %l"),whereAmI.timestamp);
      Log.verbose(F("ctime = %s"),ctime((time_t *) &whereAmI.timestamp));

      whereAmI.voltage = (uint16_t)(getBatteryVoltage() * 100.0);

      // only push if we have changed location
      float gpsdelta = abs(GPS.location.lng()-lastlong) +
            abs(GPS.location.lat()-lastlat);
      Log.verbose(F("delta = %d.%s"),(int)gpsdelta,fracString(gpsdelta,4));
      if ((gpsdelta > 0.0004 || nopushfor > 10) &&
          int(GPS.location.lng()) != 0 &&
          int(GPS.location.lat()) != 0
          ) {
        pushrtcbuffer(&whereAmI);
        lastlat = GPS.location.lat();
        lastlong= GPS.location.lng();
        lastVoltage = whereAmI.voltage;
        nopushfor = 0;
        nextGPS = millis() + GPS_SLEEPTIME;
      } else {
        Log.verbose(F("GPS delta too small (%d.%s), not pushing"),
          (int)gpsdelta,fracString(gpsdelta, 4));
          nopushfor++;
        nextGPS = millis() + GPS_SLEEPTIME;
      }

    } else {
      Log.verbose(F("GPS sats: %d location: %T time: %T date: %T updated: %T"),
	      GPS.satellites.value(),
        GPS.location.isValid(),
        GPS.time.isValid(),
        GPS.date.isValid(),
        GPS.location.isUpdated());
      nextGPS = millis() + GPS_SLEEPTIME; // 2 Minutes
    }
  }
}


// Sensor routines
void read_sensors() {

  // switch on power
  vext_power(true);

  if (voltage_found) {
    read_voltage();
  }

  read_GPS(GPS_UPDATE_TIMEOUT);
}

void test_memory() {
  sendObject_t t;
  int i = 0;

  Log.verbose(F("Testing memory start"));
  while (pushrtcbuffer(&t)) {
    i++;
    Log.verbose(F("Objects pushed: %d"),i);
  }
  Log.verbose(F("Memory full"));
  while (poprtcbuffer() != NULL);
  Log.verbose(F("Testing ended"));
  delay(1000);
}

void test_memleak() {
  sendObject_t t;
  int i = 0;

  Log.verbose(F("Testing memleak start"));
  while (pushrtcbuffer(&t)) {
    i++;
    Log.verbose(F("Objects pushed: %d"),i);
    poprtcbuffer();
  }
  Log.verbose(F("Memory full"));
  Log.verbose(F("Testing ended"));
  delay(1000);
}

void setup_serial() {
  Serial.begin(115200);
#if DEBUG
  while (!Serial);
#endif
}


// Logging helper routines
void printTimestamp(Print* _logOutput) {
  static char c[12];
  // sprintf(c, "%l ", TimerGetCurrentTime());
  sprintf(c, "%d ", millis());
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
  dis.init();
  dis.setFont(ArialMT_Plain_10);
}

void setup_gps() {
  GPS.begin(115200);
  GPS.setmode(MODE_GPS);
  GPS.setNMEA(0xff);
  read_GPS(GPS_INIT_TIMEOUT);
}

void setup_pushbutton() {
  pinMode(USER_KEY,INPUT);
}

void setup() {
  // Turn on watchdog
  innerWdtEnable(true);



  setup_serial();
  delay(5000);
  setup_logging();
  Log.verbose(F("setup(): Logging started"));
  setup_gps();
  setup_display();
  setup_chipid();
  setup_check_voltage();

  // Turn on power for devices
  pinMode(Vext,OUTPUT);
  vext_power(true);
  set_led(ledr,ledg,ledb);

  // setup_i2c();
  setup_lora();
  setup_pushbutton();
}

static bool prepareTxFrame( ) {
  // fetch top of queue
  // list is empty
  if (lastInList == NULL) {
    return false;
  }

  appDataSize = sizeof(sendObject_t);
  sendObject_t *o;
  o = poprtcbuffer();
  if (o) {
    memcpy(appData,o,appDataSize);
    return true;
  } else {
    return false;
  }
}

bool prepareEmptyFrame() {
  appDataSize = 0;
  appData[0] = 0;
  return true;
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

void process_display_command(unsigned char len, unsigned char *buffer) {
  if (len == 0) {
    Log.error(F("Zero length display command"));
    return;
  }
  switch (buffer[0]) {
    case 0:
      displayWhat = 0; // off
      dis.clear();
      dis.display();
      dis.displayOff();
      break;
    case 1:
      displayWhat = 1; // default
      break;
    case 2: {
      char *message = (char *)malloc(len+1);
      memcpy(message,buffer+1,len-1);
      message[len] = 0;
      dis.setTextAlignment(TEXT_ALIGN_CENTER);
      dis.clear();
      dis.drawStringMaxWidth(0,0,128,message);
      dis.display();
      free(message);
      displayWhat = 2;
      break;
    }
    default:
      Log.error(F("Unknown display command %d"),buffer[0]);
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
    case 3:
      process_display_command(len-1,buffer+1);
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

void downLinkAckHandle() {
  Log.verbose(F("ack received"));
  ackReceived = true;
  appTxDutyCycle = CYCLE_MIN;
}

void loop_display() {
  // standard display
  char str[30];
  dis.clear();
  dis.setFont(ArialMT_Plain_10);
  int index = sprintf(str,"%02d-%02d-%02d",
    GPS.date.year(),GPS.date.day(),GPS.date.month());
  str[index] = 0;
  dis.setTextAlignment(TEXT_ALIGN_LEFT);
  dis.drawString(0, 0, str);

  index = sprintf(str,"%02d:%02d:%02d",
    GPS.time.hour(),GPS.time.minute(),
    GPS.time.second(),GPS.time.centisecond());
  str[index] = 0;
  dis.drawString(60, 0, str);

  if( GPS.location.age() < 1000 ) {
    dis.drawString(120, 0, "A");
  } else {
    dis.drawString(120, 0, "V");
  }

#if 0
  index = sprintf(str,"alt: %d.%d",
    (int)GPS.altitude.meters(),fracPart(GPS.altitude.meters(),2));
  str[index] = 0;
  dis.drawString(0, 16, str);
#endif

  index = sprintf(str,"hdop: %d.%d",
    (int)GPS.hdop.hdop(),fracPart(GPS.hdop.hdop(),2));
  str[index] = 0;
  dis.drawString(0, 32, str);

  index = sprintf(str,"lat:%d.%d",
    (int)GPS.location.lat(),fracPart(GPS.location.lat(),4));
  str[index] = 0;
  dis.drawString(60, 16, str);

  index = sprintf(str,"lon:%d.%d",
    (int)GPS.location.lng(),fracPart(GPS.location.lng(),4));
  str[index] = 0;
  dis.drawString(60, 32, str);

#if 0
  index = sprintf(str,"speed: %d.%d km/h",
    (int)GPS.speed.kmph(),fracPart(GPS.speed.kmph(),3));
  str[index] = 0;
  dis.drawString(0, 48, str);
#endif

  index = sprintf(str,"Q:%d",queueLength());
  str[index] = 0;
  dis.drawString(0,48,str);
  dis.display();
}


void loop() {
  if (displayWhat == 1) {
    loop_display();
  }

  if (!setup_complete || (millis() > nextGPS)) {
    Log.verbose("main loop: reading GPS");
    read_sensors();
    Log.verbose("main loop: nextGPS = %l",nextGPS);
  }

  switch( deviceState )
	{
		case DEVICE_STATE_INIT:
		{
			// LoRaWAN.generateDeveuiByChipID();
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
      Log.verbose(F("DEVICE_STATE_SEND: ackReceived:%T loraCount:%d"),
        ackReceived,loraCount);

      if (ackReceived || !isTxConfirmed) {
        dataPrepared = false;
        if (prepareTxFrame()) {
          ackReceived = false;
          appTxDutyCycle = CYCLE_MIN;
  	      LoRaWAN.send();
          loraCount = 0;
          dataPrepared = true;
          send_confirmed(true);
        }
      } else {
        appTxDutyCycle =
          (appTxDutyCycle > CYCLE_MAX) ? CYCLE_MAX : (appTxDutyCycle+1000);
        loraCount++;
        if (dataPrepared && loraCount > confirmedNbTrials) {
          LoRaWAN.send();
          loraCount = 0;
        }
      }

      deviceState = DEVICE_STATE_CYCLE;
			break;
		}
		case DEVICE_STATE_CYCLE:
		{
			// Schedule next packet transmission
      Log.verbose(F("DEVICE_STATE_CYCLE: ackReceived %T"),ackReceived);
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
      // Log.verbose(F("DEVICE_STATE_SLEEP: ackReceived %T"),ackReceived);

      if (millis() + nextGPS > millis() + appTxDutyCycle) {
        delay(10);
		    LoRaWAN.sleep();
      }
			break;
		}
		default:
		{
			deviceState = DEVICE_STATE_INIT;
			break;
		}
	}

  setup_complete = true;
}
