import numpy as np
from keras.models import Sequential
from keras.layers import Dense, Activation
from keras.utils.generic_utils import get_custom_objects
from keras import backend as K

input_dim = 3
output_dim = 1

X_train = np.array([[0, 0, 1], [1, 0, 1], [0, 1, 0], [1, 1, 1]])
y_train = np.array([[1], [0], [0], [1]])

def relu1(x):
    return K.minimum(K.maximum(0.0, x), 1.0)

model = Sequential()
model.add(Dense(5, input_dim=input_dim, activation='relu1'))
model.add(Dense(2, activation='relu1'))
model.add(Dense(output_dim, activation='relu1'))

model.compile(loss='mse', optimizer='adam', metrics=['accuracy'])
model.fit(X_train, y_train, epochs=100, batch_size=1, verbose=1)

X_test = np.array([[1, 0, 0], [1, 0, 1], [0, 1, 1], [1, 1, 0]])
y_pred = model.predict(X_test)
