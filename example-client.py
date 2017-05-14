# import suds.client

# url = 'http://127.0.0.1:5000/soap/someservice?wsdl'
# client = SudsClient(url=url, cache=None)
# r = client.service.echo(str='hello world', cnt=3)
# print r


from zeep import Client

client = Client('http://localhost:9000/soap/insulincalculator?wsdl')

result = client.service.backgroundInsulinDose(50)

print (result)
