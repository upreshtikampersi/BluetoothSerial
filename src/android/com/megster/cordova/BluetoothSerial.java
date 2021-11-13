package com.megster.cordova;

import android.Manifest;
import android.app.AlertDialog;
import android.bluetooth.BluetoothManager;
import android.content.DialogInterface;
import android.content.pm.PackageManager;

import android.app.Activity;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.location.LocationManager;
import android.os.Build;
import android.os.Handler;
import android.os.Message;
import android.provider.Settings;
import android.util.Log;
import org.apache.cordova.CordovaArgs;
import org.apache.cordova.CordovaPlugin;
import org.apache.cordova.CallbackContext;
import org.apache.cordova.PluginResult;
import org.apache.cordova.LOG;
import org.jetbrains.annotations.NotNull;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Locale;
import java.util.Objects;
import java.util.Set;

import android.bluetooth.le.BluetoothLeScanner;
import android.os.Handler;

import android.bluetooth.le.ScanCallback;
import android.bluetooth.le.ScanResult;
import java.util.List;

import android.bluetooth.le.ScanSettings;
import android.bluetooth.le.ScanFilter;
import java.util.ArrayList;

import android.bluetooth.BluetoothGatt;
import android.bluetooth.BluetoothGattCallback;
import android.bluetooth.BluetoothProfile;
import android.bluetooth.BluetoothGattCharacteristic;
import android.bluetooth.BluetoothGattDescriptor;
import android.widget.TextView;

import androidx.annotation.NonNull;

import com.blessedandroid.BloodPressureMeasurement;
import com.blessedandroid.BluetoothHandler;
import com.blessedandroid.GlucoseMeasurement;
import com.blessedandroid.GlucoseMeasurementUnit;
import com.blessedandroid.HeartRateMeasurement;

import com.blessedandroid.PulseOximeterContinuousMeasurement;
import com.blessedandroid.PulseOximeterSpotMeasurement;
import com.blessedandroid.TemperatureMeasurement;
import com.blessedandroid.TemperatureUnit;
import com.blessedandroid.WeightMeasurement;
import com.welie.blessed.BluetoothCentralManager;
import com.welie.blessed.BluetoothPeripheral;

import java.util.UUID;
import java.nio.charset.StandardCharsets;

import timber.log.Timber;

/**
 * PhoneGap Plugin for Serial Communication over Bluetooth
 */
public class BluetoothSerial extends CordovaPlugin {

    // actions
    private static final String LIST = "list";
    private static final String CONNECT = "connect";
    private static final String CONNECT_INSECURE = "connectInsecure";
    private static final String DISCONNECT = "disconnect";
    private static final String WRITE = "write";
    private static final String AVAILABLE = "available";
    private static final String READ = "read";
    private static final String READ_UNTIL = "readUntil";
    private static final String SUBSCRIBE = "subscribe";
    private static final String UNSUBSCRIBE = "unsubscribe";
    private static final String SUBSCRIBE_RAW = "subscribeRaw";
    private static final String UNSUBSCRIBE_RAW = "unsubscribeRaw";
    private static final String IS_ENABLED = "isEnabled";
    private static final String IS_CONNECTED = "isConnected";
    private static final String CLEAR = "clear";
    private static final String SETTINGS = "showBluetoothSettings";
    private static final String ENABLE = "enable";
    private static final String DISCOVER_UNPAIRED = "discoverUnpaired";
    private static final String SET_DEVICE_DISCOVERED_LISTENER = "setDeviceDiscoveredListener";
    private static final String CLEAR_DEVICE_DISCOVERED_LISTENER = "clearDeviceDiscoveredListener";
    private static final String SET_NAME = "setName";
    private static final String SET_DISCOVERABLE = "setDiscoverable";

    private static final String REGISTER_RECEIVER = "registerReceiver";
    private static final String ON_RESUME = "onResume";
    private static final String ON_DESTROY = "onDestroy";

    // callbacks
    private CallbackContext connectCallback;
    private CallbackContext dataAvailableCallback;
    private CallbackContext rawDataAvailableCallback;
    private CallbackContext enableBluetoothCallback;
    private CallbackContext deviceDiscoveredCallback;

    private BluetoothAdapter bluetoothAdapter;
    private BluetoothSerialService bluetoothSerialService;

    // Debugging
    private static final String TAG = "BluetoothSerial";
    private static final boolean D = true;

    // Message types sent from the BluetoothSerialService Handler
    public static final int MESSAGE_STATE_CHANGE = 1;
    public static final int MESSAGE_READ = 2;
    public static final int MESSAGE_WRITE = 3;
    public static final int MESSAGE_DEVICE_NAME = 4;
    public static final int MESSAGE_TOAST = 5;
    public static final int MESSAGE_READ_RAW = 6;

    // Key names received from the BluetoothChatService Handler
    public static final String DEVICE_NAME = "device_name";
    public static final String TOAST = "toast";

    StringBuffer buffer = new StringBuffer();
    private String delimiter;
    private static final int REQUEST_ENABLE_BLUETOOTH = 1;

    // Android 23 requires user to explicitly grant permission for location to discover unpaired
    private static final String ACCESS_FINE_LOCATION = Manifest.permission.ACCESS_FINE_LOCATION;
    private static final int CHECK_PERMISSIONS_REQ_CODE = 2;
    private CallbackContext permissionCallback;
    
    private BluetoothLeScanner bluetoothLeScanner;
    private boolean scanning;
    private Handler handler = new Handler();
    
    private JSONArray ble_unpairedDevices = new JSONArray();
    private CallbackContext ble_ddc;
    private CallbackContext ble_read_ddc;

    // Stops scanning after 10 seconds.
    private static final long SCAN_PERIOD = 10000;
    
    UUID HEART_RATE_SERVICE_UUID = convertFromInteger(0x180D);
    UUID HEART_RATE_MEASUREMENT_CHAR_UUID = convertFromInteger(0x2A37);
    UUID HEART_RATE_CONTROL_POINT_CHAR_UUID = convertFromInteger(0x2A39);
    UUID CLIENT_CHARACTERISTIC_CONFIG_UUID = convertFromInteger(0x2902);

    @Override
    public boolean execute(String action, CordovaArgs args, CallbackContext callbackContext) throws JSONException {

        LOG.d(TAG, "action = " + action);

        if (bluetoothAdapter == null) {
            bluetoothAdapter = BluetoothAdapter.getDefaultAdapter();
        }

        if (bluetoothSerialService == null) {
            bluetoothSerialService = new BluetoothSerialService(mHandler);
        }
        
        if (bluetoothLeScanner == null) {
            bluetoothLeScanner = bluetoothAdapter.getBluetoothLeScanner();
        }

        boolean validAction = true;

        if (action.equals(LIST)) {

            listBondedDevices(callbackContext);

        } else if (action.equals(CONNECT)) {

            boolean secure = true;
            connect(args, secure, callbackContext);

        } else if (action.equals(CONNECT_INSECURE)) {

            // see Android docs about Insecure RFCOMM http://goo.gl/1mFjZY
            boolean secure = false;
            connect(args, secure, callbackContext);

        } else if (action.equals(DISCONNECT)) {

            connectCallback = null;
            bluetoothSerialService.stop();
            callbackContext.success();

        } else if (action.equals(WRITE)) {

            byte[] data = args.getArrayBuffer(0);
            bluetoothSerialService.write(data);
            callbackContext.success();

        } else if (action.equals(AVAILABLE)) {

            callbackContext.success(available());

        } else if (action.equals(READ)) {

            callbackContext.success(read());

        } else if (action.equals(READ_UNTIL)) {

            String interesting = args.getString(0);
            callbackContext.success(readUntil(interesting));

        } else if (action.equals(SUBSCRIBE)) {

            delimiter = args.getString(0);
            dataAvailableCallback = callbackContext;

            PluginResult result = new PluginResult(PluginResult.Status.NO_RESULT);
            result.setKeepCallback(true);
            callbackContext.sendPluginResult(result);

        } else if (action.equals(UNSUBSCRIBE)) {

            delimiter = null;

            // send no result, so Cordova won't hold onto the data available callback anymore
            PluginResult result = new PluginResult(PluginResult.Status.NO_RESULT);
            dataAvailableCallback.sendPluginResult(result);
            dataAvailableCallback = null;

            callbackContext.success();

        } else if (action.equals(SUBSCRIBE_RAW)) {

            ble_read_ddc = callbackContext;

            /*PluginResult result = new PluginResult(PluginResult.Status.NO_RESULT);
            result.setKeepCallback(true);
            callbackContext.sendPluginResult(result);*/

        } else if (action.equals(UNSUBSCRIBE_RAW)) {

            ble_read_ddc = null;

            callbackContext.success();

        } else if (action.equals(IS_ENABLED)) {

            if (bluetoothAdapter.isEnabled()) {
                callbackContext.success();
            } else {
                callbackContext.error("Bluetooth is disabled.");
            }

        } else if (action.equals(IS_CONNECTED)) {

            if (bluetoothSerialService.getState() == BluetoothSerialService.STATE_CONNECTED) {
                callbackContext.success();
            } else {
                callbackContext.error("Not connected.");
            }

        } else if (action.equals(CLEAR)) {

            buffer.setLength(0);
            callbackContext.success();

        } else if (action.equals(SETTINGS)) {

            Intent intent = new Intent(Settings.ACTION_BLUETOOTH_SETTINGS);
            cordova.getActivity().startActivity(intent);
            callbackContext.success();

        } else if (action.equals(ENABLE)) {

            enableBluetoothCallback = callbackContext;
            Intent intent = new Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE);
            cordova.startActivityForResult(this, intent, REQUEST_ENABLE_BLUETOOTH);

        } else if (action.equals(DISCOVER_UNPAIRED)) {

            LOG.d(TAG, "###DISCOVER_UNPAIRED###");
            
            if (cordova.hasPermission(ACCESS_FINE_LOCATION)) {
                LOG.d(TAG, "###DISCOVER_UNPAIRED_hasPermission###");
                discoverUnpairedDevices(callbackContext);
            } else {
                LOG.d(TAG, "###DISCOVER_UNPAIRED_doesNotHavePermission###");
                permissionCallback = callbackContext;
                cordova.requestPermission(this, CHECK_PERMISSIONS_REQ_CODE, ACCESS_FINE_LOCATION);
            }

        } else if (action.equals(SET_DEVICE_DISCOVERED_LISTENER)) {

            this.deviceDiscoveredCallback = callbackContext;

        } else if (action.equals(CLEAR_DEVICE_DISCOVERED_LISTENER)) {

            this.deviceDiscoveredCallback = null;

        } else if (action.equals(SET_NAME)) {

            String newName = args.getString(0);
            bluetoothAdapter.setName(newName);
            callbackContext.success();

        } else if (action.equals(SET_DISCOVERABLE)) {

            int discoverableDuration = args.getInt(0);
            Intent discoverIntent = new Intent(BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE);
            discoverIntent.putExtra(BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, discoverableDuration);
            cordova.getActivity().startActivity(discoverIntent);

        } else if (action.equals(REGISTER_RECEIVER)) {
            registerReceiver();

            OnRegisterCallback = callbackContext;

            callbackContext.success();

        } else if (action.equals(ON_RESUME)) {
            onResume();

            OnConnectCallback = callbackContext;
        } else if (action.equals(ON_DESTROY)) {
            onDestroyReceiver();

            OnDestroyCallback = callbackContext;

            callbackContext.success();
        } else {
            validAction = false;
        }

        return validAction;
    }

    private void registerReceiver() {
        cordova.getActivity().registerReceiver(locationServiceStateReceiver, new IntentFilter((LocationManager.MODE_CHANGED_ACTION)));
        cordova.getActivity().registerReceiver(bloodPressureDataReceiver, new IntentFilter( BluetoothHandler.MEASUREMENT_BLOODPRESSURE ));
        cordova.getActivity().registerReceiver(temperatureDataReceiver, new IntentFilter( BluetoothHandler.MEASUREMENT_TEMPERATURE ));
        cordova.getActivity().registerReceiver(heartRateDataReceiver, new IntentFilter( BluetoothHandler.MEASUREMENT_HEARTRATE ));
        cordova.getActivity().registerReceiver(pulseOxDataReceiver, new IntentFilter( BluetoothHandler.MEASUREMENT_PULSE_OX ));
        cordova.getActivity().registerReceiver(weightDataReceiver, new IntentFilter(BluetoothHandler.MEASUREMENT_WEIGHT));
        cordova.getActivity().registerReceiver(glucoseDataReceiver, new IntentFilter(BluetoothHandler.MEASUREMENT_GLUCOSE));
    }

    private void onResume() {
        if (getBluetoothManager().getAdapter() != null) {
            if (!isBluetoothEnabled()) {
                Intent enableBtIntent = new Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE);
                cordova.getActivity().startActivityForResult(enableBtIntent, REQUEST_ENABLE_BT);
            } else {
                checkPermissions();
            }
        } else {
            Timber.e("This device has no Bluetooth hardware");
        }
    }

    private void onDestroyReceiver() {
        cordova.getActivity().unregisterReceiver(locationServiceStateReceiver);
        cordova.getActivity().unregisterReceiver(bloodPressureDataReceiver);
        cordova.getActivity().unregisterReceiver(temperatureDataReceiver);
        cordova.getActivity().unregisterReceiver(heartRateDataReceiver);
        cordova.getActivity().unregisterReceiver(pulseOxDataReceiver);
        cordova.getActivity().unregisterReceiver(weightDataReceiver);
        cordova.getActivity().unregisterReceiver(glucoseDataReceiver);
    }

    @Override
    public void onActivityResult(int requestCode, int resultCode, Intent data) {

        if (requestCode == REQUEST_ENABLE_BLUETOOTH) {

            if (resultCode == Activity.RESULT_OK) {
                Log.d(TAG, "User enabled Bluetooth");
                if (enableBluetoothCallback != null) {
                    enableBluetoothCallback.success();
                }
            } else {
                Log.d(TAG, "User did *NOT* enable Bluetooth");
                if (enableBluetoothCallback != null) {
                    enableBluetoothCallback.error("User did not enable Bluetooth");
                }
            }

            enableBluetoothCallback = null;
        }
    }

    @Override
    public void onDestroy() {
        super.onDestroy();
        if (bluetoothSerialService != null) {
            bluetoothSerialService.stop();
        }
    }

    private void listBondedDevices(CallbackContext callbackContext) throws JSONException {
        JSONArray deviceList = new JSONArray();
        Set<BluetoothDevice> bondedDevices = bluetoothAdapter.getBondedDevices();

        for (BluetoothDevice device : bondedDevices) {
            deviceList.put(deviceToJSON(device));
        }
        callbackContext.success(deviceList);
    }

    private void discoverUnpairedDevicesOLD(final CallbackContext callbackContext) throws JSONException {

        LOG.d(TAG, "###discoverUnpairedDevices function started###");
        final CallbackContext ddc = deviceDiscoveredCallback;

        final BroadcastReceiver discoverReceiver = new BroadcastReceiver() {

            private JSONArray unpairedDevices = new JSONArray();

            @Override
            public void onReceive(Context context, Intent intent) {
                String action = intent.getAction();
                LOG.d(TAG, "###onReceive action =" + action);
                if (BluetoothDevice.ACTION_FOUND.equals(action)) {
                    BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
                    LOG.d(TAG, "###onReceive if action =" + action);
                    LOG.d(TAG, "###onReceive if device =" + device);
                    try {
                    	JSONObject o = deviceToJSON(device);
                        unpairedDevices.put(o);
                        if (ddc != null) {
                            PluginResult res = new PluginResult(PluginResult.Status.OK, o);
                            res.setKeepCallback(true);
                            ddc.sendPluginResult(res);
                        }
                    } catch (JSONException e) {
                        // This shouldn't happen, log and ignore
                        Log.e(TAG, "Problem converting device to JSON", e);
                    }
                } else if (BluetoothAdapter.ACTION_DISCOVERY_FINISHED.equals(action)) {
                    LOG.d(TAG, "###onReceive else if action =" + action);
                    LOG.d(TAG, "###onReceive unpairedDevices =" + unpairedDevices);
                    callbackContext.success(unpairedDevices);
                    cordova.getActivity().unregisterReceiver(this);
                }
            }
        };

        Activity activity = cordova.getActivity();
        activity.registerReceiver(discoverReceiver, new IntentFilter(BluetoothDevice.ACTION_FOUND));
        activity.registerReceiver(discoverReceiver, new IntentFilter(BluetoothAdapter.ACTION_DISCOVERY_FINISHED));
        activity.registerReceiver(discoverReceiver, new IntentFilter(BluetoothAdapter.ACTION_DISCOVERY_STARTED));
        if (bluetoothAdapter.isDiscovering()){
            LOG.d(TAG, "###discoverUnpairedDevices isDiscovering true###");
            bluetoothAdapter.cancelDiscovery();
        }
        boolean isDiscoveryStarted = bluetoothAdapter.startDiscovery();
        LOG.d(TAG, "###discoverUnpairedDevices discovery started 111111###   " + isDiscoveryStarted);
    }

    
    private void discoverUnpairedDevices(final CallbackContext callbackContext) throws JSONException {

        LOG.d(TAG, "###discoverUnpairedDevicesNEW function started###");
        
        ble_ddc = callbackContext;
        
        if (!scanning) {
            scanning = false;
            bluetoothLeScanner.stopScan(leScanCallback);
            
            ScanFilter filter = new ScanFilter.Builder().setDeviceName(null).build();

            ArrayList<ScanFilter> filters = new ArrayList<ScanFilter>();
            filters.add(filter);

            ScanSettings settings = new ScanSettings.Builder().setScanMode(ScanSettings.SCAN_MODE_LOW_POWER).setReportDelay(10).build();

            scanning = true;
            bluetoothLeScanner.startScan(filters, settings, leScanCallback);
            LOG.d(TAG, "###bluetoothLeScanner.startScan###");
        } else {
            scanning = false;
            bluetoothLeScanner.stopScan(leScanCallback);
            LOG.d(TAG, "###bluetoothLeScanner.stopScan###");
        }
    }
    
    public UUID convertFromInteger(int i) {
        final long MSB = 0x0000000000001000L;
        final long LSB = 0x800000805f9b34fbL;
        long value = i & 0xFFFFFFFF;
        return new UUID(MSB | (value << 32), LSB);
    }
    
    private ScanCallback leScanCallback = new ScanCallback() {
            
                @Override
                public void onScanResult(int callbackType, ScanResult result) {
                    LOG.d(TAG, "###onScanResult###  " + callbackType);
                    /*try {
                                JSONObject o = deviceToJSON(result.getDevice());
                                ble_unpairedDevices.put(o);
                            } catch (JSONException e) {
                                // This shouldn't happen, log and ignore
                                Log.e(TAG, "Problem converting device to JSON", e);
                            }
                    ble_ddc.success(ble_unpairedDevices);*/
                }
         
                @Override
                public void onBatchScanResults(List<ScanResult> results) {
                    for (ScanResult result : results) {
                           try {
                                LOG.d(TAG, "###onBatchScanResults###");
                                JSONObject o = deviceToJSON(result.getDevice());
                                ble_unpairedDevices.put(o);
                                /*if (ble_ddc != null) {
                                    PluginResult res = new PluginResult(PluginResult.Status.OK, o);
                                    res.setKeepCallback(true);
                                    ble_ddc.sendPluginResult(res);
                                }*/
                            } catch (JSONException e) {
                                // This shouldn't happen, log and ignore
                                Log.e(TAG, "Problem converting device to JSON", e);
                            }
                    }
                    ble_ddc.success(ble_unpairedDevices);
                }
        };
    
    
   private void sendHeartRateChange(int heartRate) {
       LOG.d(TAG, "###sendHeartRateChange###   " + heartRate);
        if (this.ble_read_ddc != null) {
            LOG.d(TAG, "###sendHeartRateChange ble_read_ddc not null ###   ");
            PluginResult result = new PluginResult(PluginResult.Status.OK, heartRate);
            result.setKeepCallback(true);
            this.ble_read_ddc.sendPluginResult(result);
        }
    }
    
    private final BluetoothGattCallback bluetoothGattCallback = new BluetoothGattCallback() {
        @Override
        public void onConnectionStateChange(BluetoothGatt gatt, int status, int newState) {
            if (newState == BluetoothProfile.STATE_CONNECTED) {
                gatt.discoverServices();
                /*PluginResult result = new PluginResult(PluginResult.Status.NO_RESULT);
                result.setKeepCallback(true);
                ble_ddc.sendPluginResult(result);*/
            } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                ble_ddc.error("Could not connect to the device");
            }
        }
        
         @Override
        public void onServicesDiscovered(BluetoothGatt gatt, int status){
            
            LOG.d(TAG, "###onServicesDiscovered###");
            BluetoothGattCharacteristic characteristic = gatt.getService(HEART_RATE_SERVICE_UUID).getCharacteristic(HEART_RATE_MEASUREMENT_CHAR_UUID);
            gatt.setCharacteristicNotification(characteristic, true);
            BluetoothGattDescriptor descriptor = characteristic.getDescriptor(CLIENT_CHARACTERISTIC_CONFIG_UUID);
            descriptor.setValue(BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE);
            gatt.writeDescriptor(descriptor);
        }

        @Override
        public void onCharacteristicChanged(BluetoothGatt gatt, BluetoothGattCharacteristic characteristic) {
            LOG.d(TAG, "###characteristic.getValue()###");
            int flag = characteristic.getProperties();
            int format = -1;
            if ((flag & 0x01) != 0) {
                format = BluetoothGattCharacteristic.FORMAT_UINT16;
                Log.d(TAG, "Heart rate format UINT16.");
            } else {
                format = BluetoothGattCharacteristic.FORMAT_UINT8;
                Log.d(TAG, "Heart rate format UINT8.");
            }
            final int heartRate = characteristic.getIntValue(format, 1);
            LOG.d(TAG, "###heartRate###   " + heartRate);
            /*if (ble_ddc != null) {
                PluginResult result = new PluginResult(PluginResult.Status.OK, heartRate);
                result.setKeepCallback(true);
                ble_ddc.sendPluginResult(result);
            }*/
            //ble_ddc.success(heartRate);
            sendHeartRateChange(heartRate);
        }
    };
    
    private JSONObject deviceToJSON(BluetoothDevice device) throws JSONException {
        JSONObject json = new JSONObject();
        json.put("name", device.getName());
        json.put("address", device.getAddress());
        json.put("id", device.getAddress());
        if (device.getBluetoothClass() != null) {
            json.put("class", device.getBluetoothClass().getDeviceClass());
        }
        return json;
    }

    private void connect(CordovaArgs args, boolean secure, CallbackContext callbackContext) throws JSONException {
        String macAddress = args.getString(0);
        BluetoothDevice device = bluetoothAdapter.getRemoteDevice(macAddress);
        ble_ddc = callbackContext;

        if (device != null) {
            connectCallback = callbackContext;
            BluetoothGatt bluetoothGatt = device.connectGatt(cordova.getActivity(), false, bluetoothGattCallback);
        } else {
            ble_ddc.error("Could not connect to " + macAddress);
        }
    }
    
    private void connectOLD(CordovaArgs args, boolean secure, CallbackContext callbackContext) throws JSONException {
        String macAddress = args.getString(0);
        BluetoothDevice device = bluetoothAdapter.getRemoteDevice(macAddress);

        if (device != null) {
            connectCallback = callbackContext;
            bluetoothSerialService.connect(device, secure);
            buffer.setLength(0);

            PluginResult result = new PluginResult(PluginResult.Status.NO_RESULT);
            result.setKeepCallback(true);
            callbackContext.sendPluginResult(result);

        } else {
            callbackContext.error("Could not connect to " + macAddress);
        }
    }

    // The Handler that gets information back from the BluetoothSerialService
    // Original code used handler for the because it was talking to the UI.
    // Consider replacing with normal callbacks
    private final Handler mHandler = new Handler() {

         public void handleMessage(Message msg) {
             switch (msg.what) {
                 case MESSAGE_READ:
                    buffer.append((String)msg.obj);

                    if (dataAvailableCallback != null) {
                        sendDataToSubscriber();
                    }

                    break;
                 case MESSAGE_READ_RAW:
                    if (rawDataAvailableCallback != null) {
                        byte[] bytes = (byte[]) msg.obj;
                        sendRawDataToSubscriber(bytes);
                    }
                    break;
                 case MESSAGE_STATE_CHANGE:

                    if(D) Log.i(TAG, "MESSAGE_STATE_CHANGE: " + msg.arg1);
                    switch (msg.arg1) {
                        case BluetoothSerialService.STATE_CONNECTED:
                            Log.i(TAG, "BluetoothSerialService.STATE_CONNECTED");
                            notifyConnectionSuccess();
                            break;
                        case BluetoothSerialService.STATE_CONNECTING:
                            Log.i(TAG, "BluetoothSerialService.STATE_CONNECTING");
                            break;
                        case BluetoothSerialService.STATE_LISTEN:
                            Log.i(TAG, "BluetoothSerialService.STATE_LISTEN");
                            break;
                        case BluetoothSerialService.STATE_NONE:
                            Log.i(TAG, "BluetoothSerialService.STATE_NONE");
                            break;
                    }
                    break;
                case MESSAGE_WRITE:
                    //  byte[] writeBuf = (byte[]) msg.obj;
                    //  String writeMessage = new String(writeBuf);
                    //  Log.i(TAG, "Wrote: " + writeMessage);
                    break;
                case MESSAGE_DEVICE_NAME:
                    Log.i(TAG, msg.getData().getString(DEVICE_NAME));
                    break;
                case MESSAGE_TOAST:
                    String message = msg.getData().getString(TOAST);
                    notifyConnectionLost(message);
                    break;
             }
         }
    };

    private void notifyConnectionLost(String error) {
        if (connectCallback != null) {
            connectCallback.error(error);
            connectCallback = null;
        }
    }

    private void notifyConnectionSuccess() {
        if (connectCallback != null) {
            PluginResult result = new PluginResult(PluginResult.Status.OK);
            result.setKeepCallback(true);
            connectCallback.sendPluginResult(result);
        }
    }

    private void sendRawDataToSubscriber(byte[] data) {
        if (data != null && data.length > 0) {
            PluginResult result = new PluginResult(PluginResult.Status.OK, data);
            result.setKeepCallback(true);
            rawDataAvailableCallback.sendPluginResult(result);
        }
    }

    private void sendDataToSubscriber() {
        String data = readUntil(delimiter);
        if (data != null && data.length() > 0) {
            PluginResult result = new PluginResult(PluginResult.Status.OK, data);
            result.setKeepCallback(true);
            dataAvailableCallback.sendPluginResult(result);

            sendDataToSubscriber();
        }
    }

    private int available() {
        return buffer.length();
    }

    private String read() {
        int length = buffer.length();
        String data = buffer.substring(0, length);
        buffer.delete(0, length);
        return data;
    }

    private String readUntil(String c) {
        String data = "";
        int index = buffer.indexOf(c, 0);
        if (index > -1) {
            data = buffer.substring(0, index + c.length());
            buffer.delete(0, index + c.length());
        }
        return data;
    }

    /*@Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) throws JSONException{

    }*/

    @Override
    public void onRequestPermissionResult(int requestCode, String[] permissions,
                                          int[] grantResults) throws JSONException {

        /*for(int result:grantResults) {
            if(result == PackageManager.PERMISSION_DENIED) {
                LOG.d(TAG, "User *rejected* location permission");
                this.permissionCallback.sendPluginResult(new PluginResult(
                        PluginResult.Status.ERROR,
                        "Location permission is required to discover unpaired devices.")
                    );
                return;
            }
        }

        switch(requestCode) {
            case CHECK_PERMISSIONS_REQ_CODE:
                LOG.d(TAG, "User granted location permission");
                discoverUnpairedDevices(permissionCallback);
                break;
        }*/


        cordova.getActivity().onRequestPermissionsResult(requestCode, permissions, grantResults);

        // Check if all permission were granted
        boolean allGranted = true;
        for (int result : grantResults) {
            if (result != PackageManager.PERMISSION_GRANTED) {
                allGranted = false;
                break;
            }
        }

        if (allGranted) {
            permissionsGranted();
        } else {
            new AlertDialog.Builder(cordova.getActivity())
                    .setTitle("Permission is required for scanning Bluetooth peripherals")
                    .setMessage("Please grant permissions")
                    .setPositiveButton("Retry", new DialogInterface.OnClickListener() {
                        public void onClick(DialogInterface dialogInterface, int i) {
                            dialogInterface.cancel();
                            checkPermissions();
                        }
                    })
                    .create()
                    .show();
        }
    }

    // New Code

    private CallbackContext OnRegisterCallback;
    private CallbackContext OnConnectCallback;
    private CallbackContext OnDestroyCallback;

    private TextView measurementValue;
    private static final int REQUEST_ENABLE_BT = 1;
    private static final int ACCESS_LOCATION_REQUEST = 2;
    private final DateFormat dateFormat = new SimpleDateFormat("dd-MM-yyyy HH:mm:ss", Locale.ENGLISH);

    private boolean isBluetoothEnabled() {
        BluetoothAdapter bluetoothAdapter = getBluetoothManager().getAdapter();
        if(bluetoothAdapter == null) return false;

        return bluetoothAdapter.isEnabled();
    }

    private void initBluetoothHandler()
    {
        BluetoothHandler.getInstance(cordova.getActivity().getApplicationContext());
    }

    @NotNull
    private BluetoothManager getBluetoothManager() {
        return Objects.requireNonNull((BluetoothManager) cordova.getActivity().getSystemService(Context.BLUETOOTH_SERVICE),"cannot get BluetoothManager");
    }

    private final BroadcastReceiver locationServiceStateReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            String action = intent.getAction();
            if (action != null && action.equals(LocationManager.MODE_CHANGED_ACTION)) {
                boolean isEnabled = areLocationServicesEnabled();
                Timber.i("Location service state changed to: %s", isEnabled ? "on" : "off");
                checkPermissions();
            }
        }
    };

    private final BroadcastReceiver bloodPressureDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            BluetoothPeripheral peripheral = getPeripheral(intent.getStringExtra(BluetoothHandler.MEASUREMENT_EXTRA_PERIPHERAL));
            BloodPressureMeasurement measurement = (BloodPressureMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_BLOODPRESSURE_EXTRA);
            if (measurement == null) return;

            //measurementValue.setText(String.format(Locale.ENGLISH, "%.0f/%.0f %s, %.0f bpm\n%s\n\nfrom %s", measurement.systolic, measurement.diastolic, measurement.isMMHG ? "mmHg" : "kpa", measurement.pulseRate, dateFormat.format(measurement.timestamp), peripheral.getName()));
        }
    };

    private final BroadcastReceiver temperatureDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            BluetoothPeripheral peripheral = getPeripheral(intent.getStringExtra(BluetoothHandler.MEASUREMENT_EXTRA_PERIPHERAL));
            TemperatureMeasurement measurement = (TemperatureMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_TEMPERATURE_EXTRA);
            if (measurement == null) return;

            if(OnConnectCallback != null) {
                //OnConnectCallback.success(String.valueOf(measurement.temperatureValue));


                PluginResult result = new PluginResult(PluginResult.Status.OK, measurement.temperatureValue);
                result.setKeepCallback(true);
                OnConnectCallback.sendPluginResult(result);

            }

            //measurementValue.setText(String.format(Locale.ENGLISH, "%.1f %s (%s)\n%s\n\nfrom %s", measurement.temperatureValue, measurement.unit == TemperatureUnit.Celsius ? "celsius" : "fahrenheit", measurement.type, dateFormat.format(measurement.timestamp), peripheral.getName()));
        }
    };

    private final BroadcastReceiver heartRateDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            HeartRateMeasurement measurement = (HeartRateMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_HEARTRATE_EXTRA);
            if (measurement == null) return;

            //measurementValue.setText(String.format(Locale.ENGLISH, "%d bpm", measurement.pulse));
        }
    };

    private final BroadcastReceiver pulseOxDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            BluetoothPeripheral peripheral = getPeripheral(intent.getStringExtra(BluetoothHandler.MEASUREMENT_EXTRA_PERIPHERAL));
            PulseOximeterContinuousMeasurement measurement = (PulseOximeterContinuousMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_PULSE_OX_EXTRA_CONTINUOUS);
            if (measurement != null) {
                //measurementValue.setText(String.format(Locale.ENGLISH, "SpO2 %d%%,  Pulse %d bpm\n\nfrom %s", measurement.getSpO2(), measurement.getPulseRate(), peripheral.getName()));
            }
            PulseOximeterSpotMeasurement spotMeasurement = (PulseOximeterSpotMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_PULSE_OX_EXTRA_SPOT);
            if (spotMeasurement != null) {
                //measurementValue.setText(String.format(Locale.ENGLISH, "SpO2 %d%%,  Pulse %d bpm\n%s\n\nfrom %s", spotMeasurement.getSpO2(), spotMeasurement.getPulseRate(), dateFormat.format(spotMeasurement.getTimestamp()), peripheral.getName()));
            }
        }
    };

    private final BroadcastReceiver weightDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            BluetoothPeripheral peripheral = getPeripheral(intent.getStringExtra(BluetoothHandler.MEASUREMENT_EXTRA_PERIPHERAL));
            WeightMeasurement measurement = (WeightMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_WEIGHT_EXTRA);
            if (measurement != null) {
                //measurementValue.setText(String.format(Locale.ENGLISH, "%.1f %s\n%s\n\nfrom %s", measurement.weight, measurement.unit.toString(), dateFormat.format(measurement.timestamp), peripheral.getName()));
            }
        }
    };

    private final BroadcastReceiver glucoseDataReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            BluetoothPeripheral peripheral = getPeripheral(intent.getStringExtra(BluetoothHandler.MEASUREMENT_EXTRA_PERIPHERAL));
            GlucoseMeasurement measurement = (GlucoseMeasurement) intent.getSerializableExtra(BluetoothHandler.MEASUREMENT_GLUCOSE_EXTRA);
            if (measurement != null) {
                //measurementValue.setText(String.format(Locale.ENGLISH, "%.1f %s\n%s\n\nfrom %s", measurement.value, measurement.unit == GlucoseMeasurementUnit.MmolPerLiter ? "mmol/L" : "mg/dL", dateFormat.format(measurement.timestamp), peripheral.getName()));
            }
        }
    };

    private BluetoothPeripheral getPeripheral(String peripheralAddress) {
        BluetoothCentralManager central = BluetoothHandler.getInstance(cordova.getActivity().getApplicationContext()).central;
        return central.getPeripheral(peripheralAddress);
    }

    private void checkPermissions() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            String[] missingPermissions = getMissingPermissions(getRequiredPermissions());
            if (missingPermissions.length > 0) {
                cordova.getActivity().requestPermissions(missingPermissions, ACCESS_LOCATION_REQUEST);
            } else {
                permissionsGranted();
            }
        }
    }

    private String[] getMissingPermissions(String[] requiredPermissions) {
        List<String> missingPermissions = new ArrayList<>();
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            for (String requiredPermission : requiredPermissions) {
                if (cordova.getActivity().getApplicationContext().checkSelfPermission(requiredPermission) != PackageManager.PERMISSION_GRANTED) {
                    missingPermissions.add(requiredPermission);
                }
            }
        }
        return missingPermissions.toArray(new String[0]);
    }

    private String[] getRequiredPermissions() {
        int targetSdkVersion = cordova.getActivity().getApplicationInfo().targetSdkVersion;
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S && targetSdkVersion >= Build.VERSION_CODES.S) {
            return new String[]{Manifest.permission.BLUETOOTH_SCAN, Manifest.permission.BLUETOOTH_CONNECT};
        } else if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q && targetSdkVersion >= Build.VERSION_CODES.Q) {
            return new String[]{Manifest.permission.ACCESS_FINE_LOCATION};
        } else return new String[]{Manifest.permission.ACCESS_COARSE_LOCATION};
    }

    private void permissionsGranted() {
        // Check if Location services are on because they are required to make scanning work for SDK < 31
        int targetSdkVersion = cordova.getActivity().getApplicationInfo().targetSdkVersion;
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.S && targetSdkVersion < Build.VERSION_CODES.S) {
            if (checkLocationServices()) {
                initBluetoothHandler();
            }
        } else {
            initBluetoothHandler();
        }
    }

    private boolean areLocationServicesEnabled() {
        LocationManager locationManager = (LocationManager) cordova.getActivity().getApplicationContext().getSystemService(Context.LOCATION_SERVICE);
        if (locationManager == null) {
            Timber.e("could not get location manager");
            return false;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
            return locationManager.isLocationEnabled();
        } else {
            boolean isGpsEnabled = locationManager.isProviderEnabled(LocationManager.GPS_PROVIDER);
            boolean isNetworkEnabled = locationManager.isProviderEnabled(LocationManager.NETWORK_PROVIDER);

            return isGpsEnabled || isNetworkEnabled;
        }
    }

    private boolean checkLocationServices() {
        if (!areLocationServicesEnabled()) {
            new AlertDialog.Builder(cordova.getActivity())
                    .setTitle("Location services are not enabled")
                    .setMessage("Scanning for Bluetooth peripherals requires locations services to be enabled.") // Want to enable?
                    .setPositiveButton("Enable", new DialogInterface.OnClickListener() {
                        public void onClick(DialogInterface dialogInterface, int i) {
                            dialogInterface.cancel();
                            cordova.getActivity().startActivity(new Intent(android.provider.Settings.ACTION_LOCATION_SOURCE_SETTINGS));
                        }
                    })
                    .setNegativeButton("Cancel", new DialogInterface.OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            // if this button is clicked, just close
                            // the dialog box and do nothing
                            dialog.cancel();
                        }
                    })
                    .create()
                    .show();
            return false;
        } else {
            return true;
        }
    }




}
