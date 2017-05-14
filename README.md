###### Software Quality Assurance Lecture
###### University of Coimbra
###### 2016-2017
###### Implementation of a SOAP Voter for Insulin Calculation 

### Requirements:
python 2.7 

#
Previous versions might also work, but are untested
### First Usage:
Linux | MacOS

Virtualenv is recommended
```sh
virtualenv env 
```
```sh
source env/bin/activate 
```
Windows Users
Make sure you have virtualenv in your path
```sh
virtualenv env 
```
```sh
env\Scripts\activate 
```
This will run a webservice on port 9000
```sh
pip install -r requirements.txt
```
```sh
python webservice.py 
```
This will run a webservice on port 9000

```sh
python example-client.py 
```
This will create a client to connect to the webservice and invoke the method insulindoseusage