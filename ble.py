import asyncio
from bleak import BleakScanner

async def main():
    dispositivos = await BleakScanner.discover(timeout=8, return_adv=True)
    if not dispositivos:
        print("No se encontró ningún dispositivo BLE cerca.")
        return
    for device, adv in dispositivos.values():
        print(f"{device.address}  {device.name or '(sin nombre)':24}  {adv.rssi} dBm")

asyncio.run(main())