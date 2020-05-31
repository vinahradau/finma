module CIDDomain

/*
Formal Alloy specification for Client Identification Data Requirements for banks in Switerland (further referred to as FINMA)
https://www.finma.ch/de/~/media/finma/dokumente/rundschreiben-archiv/finma-rs200821---30-06-2017.pdf
developed by Serge (vinahradau@yahooo.de)
*/

// CID data classification (FINMA 10*)
enum DATACATEGORY {DIRECT, INDIRECT, POTENTIALLY_DIRECT, PROTECTED, NONCID}

pred isCID[c : DATACATEGORY]{c = DIRECT or c = INDIRECT or c = POTENTIALLY_DIRECT}

enum METADATA {CUSTOMER_NAME, CUSTOMER_ADDRESS, IS_VIP_CUSTOMER}

enum ENTITY {ENTITY1, ENTITY2, ENTITY3}

// CID protection risks are country specific (FINMA 20*)
enum COUNTRY {SWITZERLAND, UK, USA, GERMANY}

enum CONTENT {MUSTERMANN, SEESTRASSE, YES, NO, XXXXX}

enum USER {USER1, USER2, USER3, USER4, USER5}

enum NODEID {NODE1, NODE2, NODE3}

// role and function based authorisation system in place (FINMA 22*)
enum ROLE {ROLE_GUI_USER_CID, ROLE_GUI_USER_NO_CID, ROLE_BULK_CID, ROLE_BULK_NO_CID}

pred isCIDRole[r : ROLE]{r = ROLE_GUI_USER_CID or r = ROLE_BULK_CID}

sig NODE {
nodeId: NODEID,
nodeCountry: COUNTRY,
nodeDataCategories: METADATA -> lone DATACATEGORY,
nodeDataContents: METADATA -> lone CONTENT
}

fact {
// no node outside Switzerland should have unprotected CID data stored (FINMA 20*)
no n : NODE | n.nodeCountry != SWITZERLAND and (all k : METADATA | some v : DATACATEGORY | k -> v in n.nodeDataCategories and isCID[v])
}

fact {
// all nodes with CID data stored should be recorded (FINMA 15*)
no n : NODE | (all k : METADATA | some v : DATACATEGORY | k -> v in n.nodeDataCategories and isCID[v]) and not n.nodeId in DOMAIN.cidStoringNodesIds
}

sig DOMAIN {
// CID data classification (FINMA 10*)
dataClassification: METADATA -> lone DATACATEGORY,

// CID data owner (FINMA 13*)
dataOwner: METADATA -> lone ENTITY,

nodes: NODEID -> lone NODE,

teams: ENTITY -> USER,
// an internal employee has to be responsible for the compliance of outsourced CID activities (FINMA 50*)
internalUsers: set USER,
externalUsers: set USER,

// role and function based authorisation system in place (FINMA 22*)
roles: ROLE -> METADATA,
userAccessRights: USER -> ROLE,

// CID storing Nodes have to be recorded (FINMA 15*)
cidStoringNodesIds: set NODEID,
// logs for bulk CID access (FINMA 40*)
cidBulkAccessLog: USER -> NODEID
}{
}

fact {
all u : (DOMAIN.userAccessRights).univ | u in univ.(DOMAIN.teams) // all users with access rights have to be assigned a team
all u : (DOMAIN.userAccessRights).univ | u in DOMAIN.internalUsers or u in DOMAIN.externalUsers // all users with access rights have to be classfied as internal or external
all u : DOMAIN.internalUsers | u not in DOMAIN.externalUsers // a user/employee can be either internal or external (FINMA 32*)
all u : DOMAIN.externalUsers | u not in DOMAIN.internalUsers
}

fact {
// external users with CID access rights have to have internal user in their teams:
// an internal employee has to responsible for the compliance of  outsourced CID activities (FINMA 50*)
no u : DOMAIN.externalUsers | 
(some r : DOMAIN.userAccessRights[u] | isCIDRole[r]) and (DOMAIN.teams[(DOMAIN.teams).u] & DOMAIN.internalUsers = none)
}

pred AddNodeCountry
(d, d':DOMAIN,
nodeid_in: NODEID,
country_in: COUNTRY
)
{
d'.nodes[nodeid_in].nodeCountry = country_in
}

pred AssignDataOwner
(d, d':DOMAIN,
metadata_in: METADATA,
entity_in: ENTITY)
{
d'.dataOwner = d.dataOwner ++ metadata_in -> entity_in
}

pred ClassifyData
(d, d':DOMAIN,
metadata_in: METADATA,
category_in: DATACATEGORY)
{
d'.dataClassification = d.dataClassification ++ metadata_in -> category_in
}

pred StoreData
(d, d':DOMAIN,
nodeid_in: NODEID,
metadata_in: METADATA,
content_in: CONTENT)
{
// nodes containing CID data have to be recorded (FINMA 15*)
(d.nodes[nodeid_in].nodeCountry = SWITZERLAND and isCID[d.dataClassification[metadata_in]] and d'.nodes[nodeid_in].nodeDataContents = d.nodes[nodeid_in].nodeDataContents ++ metadata_in -> content_in
and d'.nodes[nodeid_in].nodeDataCategories = d.nodes[nodeid_in].nodeDataCategories ++ metadata_in -> d.dataClassification[metadata_in] and d'.cidStoringNodesIds = d.cidStoringNodesIds + nodeid_in)
or
(not isCID[d.dataClassification[metadata_in]] and d'.nodes[nodeid_in].nodeDataContents = d.nodes[nodeid_in].nodeDataContents ++ metadata_in -> content_in
and d'.nodes[nodeid_in].nodeDataCategories = d.nodes[nodeid_in].nodeDataCategories ++ metadata_in -> d.dataClassification[metadata_in])
or
// CID data stored outside Switzerland has to be protected (FINMA 20*)
(not(d.nodes[nodeid_in].nodeCountry = SWITZERLAND) and isCID[d.dataClassification[metadata_in]] and d'.nodes[nodeid_in].nodeDataContents = d.nodes[nodeid_in].nodeDataContents ++ metadata_in -> XXXXX
and d'.nodes[nodeid_in].nodeDataCategories = d.nodes[nodeid_in].nodeDataCategories ++ metadata_in -> PROTECTED)
}

pred AddRole
(d, d':DOMAIN,
role_in: ROLE,
metadata_in: set METADATA)
{
d'.roles = d.roles++ role_in -> metadata_in
}

pred AddCIDBulkAccessLog
(d, d':DOMAIN,
user_in: USER,
node_in: NODEID
)
{
(d'.cidBulkAccessLog = d.cidBulkAccessLog ++ user_in -> node_in)
}

pred AddUser
(d, d':DOMAIN,
user_in: USER,
entity_in: ENTITY)
{
d'.teams = d.teams ++ entity_in -> user_in
}


pred AddInternalUser
(d, d':DOMAIN,
user_in: USER)
{
user_in not in d.internalUsers => d'.internalUsers = d.internalUsers + user_in 
and user_in in d.externalUsers => d'.externalUsers = d.externalUsers - user_in 
}

pred AddExternalUser
(d, d':DOMAIN,
user_in: USER)
{
user_in not in d.externalUsers => d'.externalUsers = d.externalUsers + user_in 
and user_in in d.internalUsers => d'.internalUsers = d.internalUsers - user_in 
}

pred AddUserAccessRight
(d, d':DOMAIN,
user_in: USER,
role_in: set ROLE)
{
d'.userAccessRights = d.userAccessRights ++ user_in -> role_in
}

fun accessData(
domain_in: DOMAIN, 
nodeid_in: NODEID,
user_in: USER, 
metadata_in: METADATA, 
country_in: 
COUNTRY) : CONTENT
{
// role and function based authorisation system in place (FINMA 22*)
metadata_in in domain_in.roles[domain_in.userAccessRights[user_in]] and not isCID[domain_in.nodes[nodeid_in].nodeDataCategories[metadata_in]] => domain_in.nodes[nodeid_in].nodeDataContents[metadata_in]
else
metadata_in in domain_in.roles[domain_in.userAccessRights[user_in]] and country_in = SWITZERLAND => domain_in.nodes[nodeid_in].nodeDataContents[metadata_in]
else
// CID data accessed from outside Switzerland has to be protected (FINMA 20*)
metadata_in in domain_in.roles[domain_in.userAccessRights[user_in]] and isCID[domain_in.nodes[nodeid_in].nodeDataCategories[metadata_in]] and not(country_in = SWITZERLAND) => XXXXX
else
none
}

fun accessBulkData(
domain_in: DOMAIN, 
nodeid_in: NODEID, 
user_in: USER, 
country_in: COUNTRY) : METADATA -> lone CONTENT
{
(
(ROLE_BULK_CID in domain_in.userAccessRights[user_in] or ROLE_BULK_NO_CID in domain_in.userAccessRights[user_in])
and 
(all k : METADATA | all v : DATACATEGORY | k -> v in domain_in.nodes[nodeid_in].nodeDataCategories => not isCID[v])
) => domain_in.nodes[nodeid_in].nodeDataContents
else
// logs for CID bul access (FINMA 40*)
(ROLE_BULK_CID in domain_in.userAccessRights[user_in] and country_in = SWITZERLAND
and (some k : METADATA | some v : DATACATEGORY | k -> v in domain_in.nodes[nodeid_in].nodeDataCategories and isCID[v])
and AddCIDBulkAccessLog[DOMAIN, DOMAIN, user_in, domain_in.nodes[nodeid_in].nodeId])
=> domain_in.nodes[nodeid_in].nodeDataContents
else none -> none
}

run runAndVerifyDomain for 1 DOMAIN, 2 NODE

pred runAndVerifyDomain() {
implementDataClassification
assertDataClassification

setupNodes
assertNodes

setupUserAccess
assertUserAccess

assertAccessData
assertAccessBulkData
}

pred implementDataClassification() {
AssignDataOwner[DOMAIN, DOMAIN, CUSTOMER_NAME, ENTITY1]
AssignDataOwner[DOMAIN, DOMAIN, IS_VIP_CUSTOMER, ENTITY1]
AssignDataOwner[DOMAIN, DOMAIN, CUSTOMER_ADDRESS, ENTITY1]
ClassifyData[DOMAIN, DOMAIN, CUSTOMER_NAME, DIRECT]
ClassifyData[DOMAIN, DOMAIN, CUSTOMER_ADDRESS, DIRECT]
ClassifyData[DOMAIN, DOMAIN, IS_VIP_CUSTOMER, NONCID]
}

pred assertDataClassification{
// Customer name is classified as direct CID data
DOMAIN.dataClassification[CUSTOMER_NAME] = DIRECT
// Entity 1 is responsible for the customer name data
DOMAIN.dataOwner[CUSTOMER_NAME] = ENTITY1
// Customer address is classified as direct CID data
DOMAIN.dataClassification[CUSTOMER_ADDRESS] = DIRECT
// Entity 1 is responsible for the customer address data
DOMAIN.dataOwner[CUSTOMER_ADDRESS] = ENTITY1
// VIP flag is classified as non-CID data
DOMAIN.dataClassification[IS_VIP_CUSTOMER] = NONCID
// Entity 1 is responsible for the VIP flag data
DOMAIN.dataOwner[IS_VIP_CUSTOMER] = ENTITY1
}

pred setupNodes() {
#DOMAIN.nodes = 2

DOMAIN.nodes[NODE1].nodeId = NODE1
DOMAIN.nodes[NODE2].nodeId = NODE2

// NODE1 in Switzerland 
AddNodeCountry[DOMAIN, DOMAIN, NODE1, SWITZERLAND]

// NODE2 outside Switzerland
AddNodeCountry[DOMAIN, DOMAIN, NODE2, USA]

StoreData[DOMAIN, DOMAIN, NODE1, CUSTOMER_NAME, MUSTERMANN]
StoreData[DOMAIN, DOMAIN, NODE1, CUSTOMER_ADDRESS, SEESTRASSE]
StoreData[DOMAIN, DOMAIN, NODE1, IS_VIP_CUSTOMER, YES]

StoreData[DOMAIN, DOMAIN, NODE2, CUSTOMER_NAME, MUSTERMANN]
StoreData[DOMAIN, DOMAIN, NODE2, CUSTOMER_ADDRESS, SEESTRASSE]
StoreData[DOMAIN, DOMAIN, NODE2, IS_VIP_CUSTOMER, YES]
}

pred assertNodes() {
// node in Switzerland has the customer name value stored as direct CID data
DOMAIN.nodes[NODE1].nodeDataCategories[CUSTOMER_NAME] = DIRECT
DOMAIN.nodes[NODE1].nodeDataContents[CUSTOMER_NAME] = MUSTERMANN

// node in Switzerland has the customer address value stored as direct CID data
DOMAIN.nodes[NODE1].nodeDataCategories[CUSTOMER_ADDRESS] = DIRECT
DOMAIN.nodes[NODE1].nodeDataContents[CUSTOMER_ADDRESS] = SEESTRASSE

// node in Switzerland has the vip flag value stored as non-CID
DOMAIN.nodes[NODE1].nodeDataCategories[IS_VIP_CUSTOMER] = NONCID
DOMAIN.nodes[NODE1].nodeDataContents[IS_VIP_CUSTOMER] = YES

// node in USA has the customer name value stored as protected CID data
DOMAIN.nodes[NODE2].nodeDataCategories[CUSTOMER_NAME] = PROTECTED
DOMAIN.nodes[NODE2].nodeDataContents[CUSTOMER_NAME] = XXXXX

// node in USA has the customer address value stored as protected CID data
DOMAIN.nodes[NODE2].nodeDataCategories[CUSTOMER_ADDRESS] = PROTECTED
DOMAIN.nodes[NODE2].nodeDataContents[CUSTOMER_ADDRESS] = XXXXX

// node in USA has the vip flag stored as non- CID data
DOMAIN.nodes[NODE2].nodeDataCategories[IS_VIP_CUSTOMER] = NONCID
DOMAIN.nodes[NODE2].nodeDataContents[IS_VIP_CUSTOMER] = YES

// node in Switzerland storing CID data is recorded
NODE1 in DOMAIN.cidStoringNodesIds
// node in USA not storing CID data is not recorded
NODE2 not in DOMAIN.cidStoringNodesIds
}

pred setupUserAccess() {
AddUser[DOMAIN, DOMAIN, (USER1 + USER2 + USER5), ENTITY2]

// internal employee respinsible for compliance of external CID activities (FINMA 50*)
AddInternalUser[DOMAIN, DOMAIN, USER5]
AddExternalUser[DOMAIN, DOMAIN, USER1]
AddExternalUser[DOMAIN, DOMAIN, USER2]

#DOMAIN.internalUsers = 1
#DOMAIN.externalUsers = 2
#DOMAIN.teams = 3

AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER_CID, (CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER)]
AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER_NO_CID, (IS_VIP_CUSTOMER)]

AddUserAccessRight[DOMAIN, DOMAIN, USER1, (ROLE_GUI_USER_CID + ROLE_GUI_USER_NO_CID + ROLE_BULK_CID)]
AddUserAccessRight[DOMAIN, DOMAIN, USER2, (ROLE_GUI_USER_NO_CID + ROLE_BULK_NO_CID)]
}

pred assertUserAccess() {
// CID GUI role allows to access customer name, customr address, vip flag
DOMAIN.roles[ROLE_GUI_USER_CID] = CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER
// Non-CID GUI role allows to access vip flag
DOMAIN.roles[ROLE_GUI_USER_NO_CID] = IS_VIP_CUSTOMER

// user 1 gets GUI CID role, GUI non-CID role, bulk CID access role
DOMAIN.userAccessRights[USER1] = ROLE_GUI_USER_CID + ROLE_GUI_USER_NO_CID + ROLE_BULK_CID
// user 2 gets GUI non-CID role, bulk non-CID access role
DOMAIN.userAccessRights[USER2] = ROLE_GUI_USER_NO_CID + ROLE_BULK_NO_CID

// no roles for user 3
DOMAIN.userAccessRights[USER3] = none
}

pred assertAccessData() {
// user in Switzerland with access rights accesses CID data 
accessData[DOMAIN, NODE1, USER1, CUSTOMER_NAME, SWITZERLAND] = MUSTERMANN
// user in Switzerland with access rights accesses CID data  
accessData[DOMAIN, NODE1, USER1, CUSTOMER_ADDRESS, SWITZERLAND] = SEESTRASSE
// user in Switzerland with access rights accesses non-CID data  
accessData[DOMAIN, NODE1, USER1, IS_VIP_CUSTOMER, SWITZERLAND] = YES

// user in USA with access rights accesses a protected version of CID data  
accessData[DOMAIN, NODE1, USER1, CUSTOMER_NAME, USA] = XXXXX
// user in USA with access rights accesses a protected version of CID data  
accessData[DOMAIN, NODE1, USER1, CUSTOMER_ADDRESS, USA] = XXXXX
// user in USA with access rights accesses non-CID data  
accessData[DOMAIN, NODE1, USER1, IS_VIP_CUSTOMER, USA] = YES

// user in Switzerland without CID access rights can not access CID data  
accessData[DOMAIN, NODE1, USER2, CUSTOMER_NAME, SWITZERLAND] = none
// user in Switzerland without CID access rights can not access CID data 
accessData[DOMAIN, NODE1, USER2, CUSTOMER_ADDRESS, SWITZERLAND] = none
// user in Switzerland with access rights accesses non-CID data  
accessData[DOMAIN, NODE1, USER2, IS_VIP_CUSTOMER, SWITZERLAND] = YES

// user in USA without CID access rights can not access CID data  
accessData[DOMAIN, NODE1, USER2, CUSTOMER_NAME, USA] = none
// user in USA without CID access rights can not access CID data  
accessData[DOMAIN, NODE1, USER2, CUSTOMER_ADDRESS, USA] = none
// user in USA with access rights accesses non-CID data
accessData[DOMAIN, NODE1, USER2, IS_VIP_CUSTOMER, USA] = YES

// user in SWITZERLAND without access rights can not access data
accessData[DOMAIN, NODE1, USER3, CUSTOMER_NAME, SWITZERLAND] = none
// user in USA without access rights can not access data  
accessData[DOMAIN, NODE1, USER3, CUSTOMER_NAME, USA] = none

// user in SWITZERLAND with access rights accesses CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER1, CUSTOMER_NAME, SWITZERLAND] = XXXXX
// user in SWITZERLAND with access rights accesses CID data stored as protected on a USA node
accessData[DOMAIN, NODE2, USER1, CUSTOMER_ADDRESS, SWITZERLAND] = XXXXX
// user in SWITZERLAND with access rights accesses non-CID data  
accessData[DOMAIN, NODE2, USER1, IS_VIP_CUSTOMER, SWITZERLAND] = YES

// user in USA with access rights accesses CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER1, CUSTOMER_NAME, USA] = XXXXX
// user in USA with access rights accesses CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER1, CUSTOMER_ADDRESS, USA] = XXXXX
// user in USA with access rights accesses non-CID data 
accessData[DOMAIN, NODE2, USER1, IS_VIP_CUSTOMER, USA] = YES

// user in Switzerland without access rights can not accesses CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER2, CUSTOMER_NAME, SWITZERLAND] = none
// user in Switzerland without access rights can not accesses CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER2, CUSTOMER_ADDRESS, SWITZERLAND] = none
// user in Switzerland with access rights accesses non-CID data  
accessData[DOMAIN, NODE2, USER2, IS_VIP_CUSTOMER, SWITZERLAND] = YES

// user in USA without access rights can not access CID data stored as protected on a USA node  
accessData[DOMAIN, NODE2, USER2, CUSTOMER_NAME, USA] = none
// user in USA without CID access rights can not access CID data stored as protected on a USA node 
accessData[DOMAIN, NODE2, USER2, CUSTOMER_ADDRESS, USA] = none
// user in USA with access rights accesses non-CID data  
accessData[DOMAIN, NODE2, USER2, IS_VIP_CUSTOMER, USA] = YES

// user without access rights can not access data  
accessData[DOMAIN, NODE2, USER3, CUSTOMER_NAME, SWITZERLAND] = none
// user without access rights can not access data  
accessData[DOMAIN, NODE2, USER3, CUSTOMER_NAME, USA] = none
}

pred assertAccessBulkData() {
// user in Switzerland with bulk CID rights accesses bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER1, SWITZERLAND] = 3
// user in Switzerland without bulk CID rights can not access bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER2, SWITZERLAND] = 0
// user in Switzerland without bulk rights can not access bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER3, SWITZERLAND] = 0

// user in USA with bulk CID rights can not access bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER1, USA] = 0
// user in USA with bulk rights in USA can not access bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER2, USA] = 0
// user in USA without bulk rights in USA can not access bulk CID data  
#accessBulkData[DOMAIN, NODE1, USER3, USA] = 0

// user in Switzerland with bulk CID rights can access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER1, SWITZERLAND] = 3
// user in Switzerland with bulk rights can access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER2, SWITZERLAND] = 3
// user in Switzerland without bulk rights can not access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER3, SWITZERLAND] = 0

// user in USA with bulk CID rights in USA can access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER1, USA] = 3
// user in USA with bulk rights in USA can access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER2, USA] = 3
// user in USA without bulk rights in USA can not access bulk non CID data  
#accessBulkData[DOMAIN, NODE2, USER3, USA] = 0

// user accessing bulk CID data results in a log record  
#DOMAIN.cidBulkAccessLog = 1
USER1 -> NODE1 in DOMAIN.cidBulkAccessLog
}
