from zeep import Client

client = Client('http://localhost:9000/soap/insulincalculator?wsdl')

result = client.service.backgroundInsulinDose(50)

print (result)
