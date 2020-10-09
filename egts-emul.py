import copy
import struct
import abc
import collections
import enum
import binascii

import socket
import time
import datetime


CRC8_TABLE = (
    0x00, 0x31, 0x62, 0x53, 0xC4, 0xF5, 0xA6, 0x97,
    0xB9, 0x88, 0xDB, 0xEA, 0x7D, 0x4C, 0x1F, 0x2E,
    0x43, 0x72, 0x21, 0x10, 0x87, 0xB6, 0xE5, 0xD4,
    0xFA, 0xCB, 0x98, 0xA9, 0x3E, 0x0F, 0x5C, 0x6D,
    0x86, 0xB7, 0xE4, 0xD5, 0x42, 0x73, 0x20, 0x11,
    0x3F, 0x0E, 0x5D, 0x6C, 0xFB, 0xCA, 0x99, 0xA8,
    0xC5, 0xF4, 0xA7, 0x96, 0x01, 0x30, 0x63, 0x52,
    0x7C, 0x4D, 0x1E, 0x2F, 0xB8, 0x89, 0xDA, 0xEB,
    0x3D, 0x0C, 0x5F, 0x6E, 0xF9, 0xC8, 0x9B, 0xAA,
    0x84, 0xB5, 0xE6, 0xD7, 0x40, 0x71, 0x22, 0x13,
    0x7E, 0x4F, 0x1C, 0x2D, 0xBA, 0x8B, 0xD8, 0xE9,
    0xC7, 0xF6, 0xA5, 0x94, 0x03, 0x32, 0x61, 0x50,
    0xBB, 0x8A, 0xD9, 0xE8, 0x7F, 0x4E, 0x1D, 0x2C,
    0x02, 0x33, 0x60, 0x51, 0xC6, 0xF7, 0xA4, 0x95,
    0xF8, 0xC9, 0x9A, 0xAB, 0x3C, 0x0D, 0x5E, 0x6F,
    0x41, 0x70, 0x23, 0x12, 0x85, 0xB4, 0xE7, 0xD6,
    0x7A, 0x4B, 0x18, 0x29, 0xBE, 0x8F, 0xDC, 0xED,
    0xC3, 0xF2, 0xA1, 0x90, 0x07, 0x36, 0x65, 0x54,
    0x39, 0x08, 0x5B, 0x6A, 0xFD, 0xCC, 0x9F, 0xAE,
    0x80, 0xB1, 0xE2, 0xD3, 0x44, 0x75, 0x26, 0x17,
    0xFC, 0xCD, 0x9E, 0xAF, 0x38, 0x09, 0x5A, 0x6B,
    0x45, 0x74, 0x27, 0x16, 0x81, 0xB0, 0xE3, 0xD2,
    0xBF, 0x8E, 0xDD, 0xEC, 0x7B, 0x4A, 0x19, 0x28,
    0x06, 0x37, 0x64, 0x55, 0xC2, 0xF3, 0xA0, 0x91,
    0x47, 0x76, 0x25, 0x14, 0x83, 0xB2, 0xE1, 0xD0,
    0xFE, 0xCF, 0x9C, 0xAD, 0x3A, 0x0B, 0x58, 0x69,
    0x04, 0x35, 0x66, 0x57, 0xC0, 0xF1, 0xA2, 0x93,
    0xBD, 0x8C, 0xDF, 0xEE, 0x79, 0x48, 0x1B, 0x2A,
    0xC1, 0xF0, 0xA3, 0x92, 0x05, 0x34, 0x67, 0x56,
    0x78, 0x49, 0x1A, 0x2B, 0xBC, 0x8D, 0xDE, 0xEF,
    0x82, 0xB3, 0xE0, 0xD1, 0x46, 0x77, 0x24, 0x15,
    0x3B, 0x0A, 0x59, 0x68, 0xFF, 0xCE, 0x9D, 0xAC
)

CRC16_TABLE = (
    0x0000, 0x1021, 0x2042, 0x3063, 0x4084, 0x50a5,
    0x60c6, 0x70e7, 0x8108, 0x9129, 0xa14a, 0xb16b,
    0xc18c, 0xd1ad, 0xe1ce, 0xf1ef, 0x1231, 0x0210,
    0x3273, 0x2252, 0x52b5, 0x4294, 0x72f7, 0x62d6,
    0x9339, 0x8318, 0xb37b, 0xa35a, 0xd3bd, 0xc39c,
    0xf3ff, 0xe3de, 0x2462, 0x3443, 0x0420, 0x1401,
    0x64e6, 0x74c7, 0x44a4, 0x5485, 0xa56a, 0xb54b,
    0x8528, 0x9509, 0xe5ee, 0xf5cf, 0xc5ac, 0xd58d,
    0x3653, 0x2672, 0x1611, 0x0630, 0x76d7, 0x66f6,
    0x5695, 0x46b4, 0xb75b, 0xa77a, 0x9719, 0x8738,
    0xf7df, 0xe7fe, 0xd79d, 0xc7bc, 0x48c4, 0x58e5,
    0x6886, 0x78a7, 0x0840, 0x1861, 0x2802, 0x3823,
    0xc9cc, 0xd9ed, 0xe98e, 0xf9af, 0x8948, 0x9969,
    0xa90a, 0xb92b, 0x5af5, 0x4ad4, 0x7ab7, 0x6a96,
    0x1a71, 0x0a50, 0x3a33, 0x2a12, 0xdbfd, 0xcbdc,
    0xfbbf, 0xeb9e, 0x9b79, 0x8b58, 0xbb3b, 0xab1a,
    0x6ca6, 0x7c87, 0x4ce4, 0x5cc5, 0x2c22, 0x3c03,
    0x0c60, 0x1c41, 0xedae, 0xfd8f, 0xcdec, 0xddcd,
    0xad2a, 0xbd0b, 0x8d68, 0x9d49, 0x7e97, 0x6eb6,
    0x5ed5, 0x4ef4, 0x3e13, 0x2e32, 0x1e51, 0x0e70,
    0xff9f, 0xefbe, 0xdfdd, 0xcffc, 0xbf1b, 0xaf3a,
    0x9f59, 0x8f78, 0x9188, 0x81a9, 0xb1ca, 0xa1eb,
    0xd10c, 0xc12d, 0xf14e, 0xe16f, 0x1080, 0x00a1,
    0x30c2, 0x20e3, 0x5004, 0x4025, 0x7046, 0x6067,
    0x83b9, 0x9398, 0xa3fb, 0xb3da, 0xc33d, 0xd31c,
    0xe37f, 0xf35e, 0x02b1, 0x1290, 0x22f3, 0x32d2,
    0x4235, 0x5214, 0x6277, 0x7256, 0xb5ea, 0xa5cb,
    0x95a8, 0x8589, 0xf56e, 0xe54f, 0xd52c, 0xc50d,
    0x34e2, 0x24c3, 0x14a0, 0x0481, 0x7466, 0x6447,
    0x5424, 0x4405, 0xa7db, 0xb7fa, 0x8799, 0x97b8,
    0xe75f, 0xf77e, 0xc71d, 0xd73c, 0x26d3, 0x36f2,
    0x0691, 0x16b0, 0x6657, 0x7676, 0x4615, 0x5634,
    0xd94c, 0xc96d, 0xf90e, 0xe92f, 0x99c8, 0x89e9,
    0xb98a, 0xa9ab, 0x5844, 0x4865, 0x7806, 0x6827,
    0x18c0, 0x08e1, 0x3882, 0x28a3, 0xcb7d, 0xdb5c,
    0xeb3f, 0xfb1e, 0x8bf9, 0x9bd8, 0xabbb, 0xbb9a,
    0x4a75, 0x5a54, 0x6a37, 0x7a16, 0x0af1, 0x1ad0,
    0x2ab3, 0x3a92, 0xfd2e, 0xed0f, 0xdd6c, 0xcd4d,
    0xbdaa, 0xad8b, 0x9de8, 0x8dc9, 0x7c26, 0x6c07,
    0x5c64, 0x4c45, 0x3ca2, 0x2c83, 0x1ce0, 0x0cc1,
    0xef1f, 0xff3e, 0xcf5d, 0xdf7c, 0xaf9b, 0xbfba,
    0x8fd9, 0x9ff8, 0x6e17, 0x7e36, 0x4e55, 0x5e74,
    0x2e93, 0x3eb2, 0x0ed1, 0x1ef0
)


class EGTStrack(object):
    def __init__(self, deviceid, deviceimei=None):
        self._tid = int(deviceid)
        self._imei = str(deviceimei)
        self._pt = b'\x01' # Ид пакета # EGTSAppdata
        self._hcs = b'\x00' # header conlrol sum size = 1 Byte
        self._sfrcs = 0 # service force control sum
        self._service = None # services
        self._fdl = b'\x0000'
        self._pid = int( 1 )
        self._rn = self._pid
        self.add_service(1)
        
    def get_date_time(self, value):
        initial_date = datetime.datetime(year=2010, month=1, day=1, hour=0, minute=0, second=0)
        seconds = int((value - initial_date-datetime.timedelta(minutes=180)).total_seconds())
        return int(seconds)
        
    def add_service(self, record_types, *args, **kwargs):
        if self._service == None:
            self._service = b''
        sst = b'\x01' # Source service type 1 byte
        rst = b'\x01' # recipient service type 1 byte
        rfl = b'\x00' # record flags
        rl = b'\x0000' # record length 
        rn = self._rn.to_bytes(2, byteorder='little') # record number
        if record_types == 1:
            _oid = self._tid.to_bytes(4, byteorder='little')
            tm = self.get_date_time(datetime.datetime.now()).to_bytes(4, byteorder='little')
            rfl = b'\x05' # record flag        
            self._pt = b'\x01' # Ид пакета # EGTSAppdata
            recLen = b'' # 2 bytes            
            srt = record_types.to_bytes(1, byteorder='little')
            mservice = b''
            mservice += self._tid.to_bytes(4, byteorder='little')
            mservice += b'\x9e'
            mservice += self._imei.encode('utf-8')
            mservice += '0000000000000000'.encode('utf-8') # IMSI
            mservice += 'rus'.encode('utf-8')
            mservice += '000000000000000'.encode('utf-8')  # MSISDN
            srl = len(mservice).to_bytes(2, byteorder='little')
            _service = srt + srl + mservice 
            rl = len(_service).to_bytes(2, byteorder='little')# record length
            headService = rl + rn + rfl + _oid + tm + sst + rst
        elif record_types == 2:
            rfl = b'\x05' # record flags
            _oid =self._tid.to_bytes(4, byteorder='little')
            tm = self.get_date_time(datetime.datetime.now()).to_bytes(4, byteorder='little')
            srt = record_types.to_bytes(1, byteorder='little')
            mservice = b''
            mservice += b'\x03' # MT
            mservice += b'\x11111111' # VID
            mservice += b'\x1111' # FWV
            mservice += b'\x1111' # SWV
            mservice += b'\x01' # MD
            mservice += b'\x01' # ST (state)
            mservice += b'\x00' # D (разделитель строк)
            mservice += b'\x00' # D (разделитель строк)
            mservice += b'\x11111111' # VID
            srl = len(mservice).to_bytes(2, byteorder='little')
            _service = srt + srl + mservice 
            rl = len(_service).to_bytes(2, byteorder='little')# record length
            headService = rl + rn + rfl + _oid + tm + sst + rst            
        elif record_types == 16:
            sst = b'\x02' # Source service type 1 byte
            rst = b'\x02' # recipient service type 1 byte
            _oid = self._tid.to_bytes(4, byteorder='little')
            tm = self.get_date_time(datetime.datetime.now()).to_bytes(4, byteorder='little')
            rfl = b'\x05' # record flags
            self._pt = b'\x01' # Ид пакета # EGTSAppdata
            srt = record_types.to_bytes(1, byteorder='little')
            llflags = 1 # Флаги
            if kwargs['long'] < 0 : 
                llflags = llflags | 2
            if kwargs['lat'] < 0 : 
                llflags = llflags | 4
            _long = (int(abs(kwargs['long']) / 180 * 0xFFFFFFFF ).to_bytes(4, byteorder='little')) # 
            lat = int(abs(kwargs['lat']) / 90 * 0xFFFFFFFF ).to_bytes(4, byteorder='little') #            
            ntm = self.get_date_time(datetime.datetime.now()).to_bytes(4, byteorder='little')
            print(llflags)
            flags =  llflags.to_bytes(1, byteorder='little')
            spd = int(kwargs['speed']*10).to_bytes(2, byteorder='little') # speed 
            dir = int(0).to_bytes(1, byteorder='little') # directory 1 byte
            odm = int(1200).to_bytes(3, byteorder='little') # 3 bytes
            din = b'\x01' # цифровые датчики 1 byte
            src = b'\x00' # 1 byte Источник сообщения "по таймеру при включенном зажигании"
            # Собираем пакет
            mservice = ntm + lat + _long +  flags + spd + dir + odm + din + src
            srl = len(mservice).to_bytes(2, byteorder='little')
            _service = srt + srl + mservice 
            rl = len(_service).to_bytes(2, byteorder='little')# record length
            headService = rl + rn + rfl + _oid + tm + sst + rst
        elif record_types == 4: # GTS_SR_AUTH_SERV_IDENTITY	4	/* Not described in protocol docs*/
            self._pt = b'\x01' # Ид пакета # EGTSAppdata
            recLen = b'' # 2 bytes            
            # subservice_type
            srt = record_types.to_bytes(1, byteorder='little')
            mservice = b''
            mservice += b'\x02'
            mservice += b'\x02'
            mservice += self._tid.to_bytes(4, byteorder='little')
            mservice += b'\x02'
            mservice += self._imei.encode('utf-8')
            srl = len(mservice).to_bytes(2, byteorder='little')
            _service = srt + srl + mservice 
            rl = len(_service).to_bytes(2, byteorder='little')# record length
            headService = rl + rn + rfl + sst + rst
        self._service += headService + _service
        self._rn += 1
        pass
      
        
    def new_message(self):
        if self._service == None:
            raise TypeError('Unknown packet type: {}'.format(self._service))
        self._pid = self._rn
        print('number packet^',self._pid)
        if self._service != None:
            self._sfrcs = self.data_crc(self._service).to_bytes(2, byteorder='little')
            self._fdl = len(self._service).to_bytes(2, byteorder='little')
        getBytes = self.bytes    
        self._hcs = self.header_crc(getBytes).to_bytes(1, byteorder='little')
        getBytes = getBytes + self._hcs  + self._service + self._sfrcs
        self._service = None
        return getBytes
        pass
        
    def header(self):
        pass
        
    @property    
    def bytes(self):
        packetPVR = b'\x01'
        packetSKID = b'\x00'
        packetFLAGS = b'\x00'
        packetHL = b'\x0b'
        packetHE = b'\x00'
        getBytes = b''
        getBytes += packetPVR
        getBytes += packetSKID
        getBytes += packetFLAGS
        getBytes += packetHL
        getBytes += packetHE
        getBytes += self._fdl #.to_bytes(2, byteorder='big')
        #print(self._pid.to_bytes(2, byteorder='little'))
        getBytes += self._pid.to_bytes(2, byteorder='little')
        getBytes += self._pt
        #print(len(getBytes))
        return getBytes
        pass
        
    def __str__(self):
        return self.new_message().hex()
        pass

    def header_crc(self,header):
        """
        Calculate header checksum
        """
        crc = 0xFF
        i = 0
        while i < len(header):
            crc = CRC8_TABLE[crc ^ header[i]]
            i += 1
        return crc


    def data_crc(self,data):
        """
        Calculate data checksum
        """
        crc = 0xFFFF
        i = 0
        while i < len(data):
            crc = ((crc << 8) % 0x10000) ^ CRC16_TABLE[(crc >> 8) ^ data[i]]
            i += 1
        return crc
        


sock = socket.socket()
sock.connect(('egts.yandex.net', 4000)) # Connecting Yandex.Routing
cmd1 = EGTStrack(deviceid = "111111111", deviceimei="865811111111111") # Create a class and configure the device
message_b = cmd1.new_message() # get message
print('CLT >> "{}"'.format(message_b.hex()))
sock.sendall(message_b) # sends a message to the server
recv_b = sock.recv(256) # 
print('SRV >> "{}"'.format(recv_b.hex()))
# Example geopoints
masspoint = [{'long':40.055205,'lat':47.423826, 'speed':90},
             {'long':39.7202,'lat':46.969264, 'speed':90},
             {'long':39.135668,'lat':45.1951, 'speed':90},
             {'long':39.41101,'lat':45.486162, 'speed':90},
             {'long':40.170455,'lat':45.844528, 'speed':90},
             {'long':39.941324,'lat':46.31055, 'speed':90},
             {'long':39.683845,'lat':46.538551, 'speed':90},
             {'long':40.055205,'lat':47.423826, 'speed':90}]

for gpoint in masspoint:
    cmd1.add_service(16, long=gpoint['long'],lat=gpoint['lat'],speed=gpoint['speed'])
    message_b = cmd1.new_message()
    print('CLT >> "{}"'.format(message_b.hex()))
    sock.sendall(message_b)
    recv_b = sock.recv(256)
    print('SRV >> "{}"'.format(recv_b.hex()))
    time.sleep(20)
sock.close()

